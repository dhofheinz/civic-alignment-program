"""Numerical probe of crossing versus genuine basin-exit quasipotentials.

This is a reproducible numerical investigation, not a proof artifact.  It reconstructs the
local stable-manifold branch of the unforced saddle by inverse iteration and
solves two finite-horizon control problems with analytic adjoints:

* reach the saddle policy (the crossing quasipotential); and
* reach the stable-manifold graph (the basin-exit quasipotential).

The second target is the actual basin boundary, rather than the stronger and
generally more expensive requirement of reaching the saddle itself.
"""

from __future__ import annotations

import argparse
from dataclasses import dataclass

import numpy as np
from scipy.interpolate import PchipInterpolator
from scipy.optimize import brentq, minimize, root_scalar


ETA = 0.5
C = 0.9
LAMBDA0 = 0.02
INJECTION = 0.04
VALUE = 0.1
RHO = 0.0


def stock_multiplier(beta: float | np.ndarray) -> float | np.ndarray:
    return (1 - LAMBDA0) * (1 - ETA * (1 - beta)) ** 2


def stock_multiplier_prime(beta: float | np.ndarray) -> float | np.ndarray:
    return 2 * (1 - LAMBDA0) * ETA * (1 - ETA * (1 - beta))


def stock_coefficient(beta: float | np.ndarray) -> float | np.ndarray:
    return 2 * C * (1 - C * beta) - RHO


def stationary_stock(beta: float | np.ndarray) -> float | np.ndarray:
    return INJECTION / (1 - stock_multiplier(beta))


def gradient(beta: float | np.ndarray, stock: float | np.ndarray) -> float | np.ndarray:
    return -VALUE + stock_coefficient(beta) * stock


SADDLE_POLICY = brentq(
    lambda beta: gradient(beta, stationary_stock(beta)), 0.0, 1.0
)
SADDLE_STOCK = float(stationary_stock(SADDLE_POLICY))
CALIBRATED_STOCK = float(stationary_stock(0.0))


@dataclass
class Orbit:
    policy: np.ndarray
    stock: np.ndarray
    clipped: np.ndarray


def forward(alpha: float, controls: np.ndarray) -> Orbit:
    horizon = len(controls)
    policy = np.empty(horizon + 1)
    stock = np.empty(horizon + 1)
    clipped = np.zeros(horizon + 1, dtype=bool)
    policy[0] = 0.0
    stock[0] = CALIBRATED_STOCK
    for time in range(horizon):
        raw = policy[time] + alpha * (
            gradient(policy[time], stock[time]) + controls[time]
        )
        policy[time + 1] = np.clip(raw, 0.0, 1.0)
        clipped[time + 1] = raw < 0.0 or 1.0 < raw
        stock[time + 1] = (
            stock_multiplier(policy[time]) * stock[time] + INJECTION
        )
    return Orbit(policy, stock, clipped)


def unforced_jacobian(alpha: float) -> np.ndarray:
    return np.array(
        [
            [
                1 - 2 * alpha * C**2 * SADDLE_STOCK,
                alpha * stock_coefficient(SADDLE_POLICY),
            ],
            [
                stock_multiplier_prime(SADDLE_POLICY) * SADDLE_STOCK,
                stock_multiplier(SADDLE_POLICY),
            ],
        ]
    )


def reverse_jacobian(alpha: float) -> np.ndarray:
    """Jacobian of beta' = beta - alpha*g(beta,D), D' = s(beta)D+I."""
    return np.array(
        [
            [
                1 + 2 * alpha * C**2 * SADDLE_STOCK,
                -alpha * stock_coefficient(SADDLE_POLICY),
            ],
            [
                stock_multiplier_prime(SADDLE_POLICY) * SADDLE_STOCK,
                stock_multiplier(SADDLE_POLICY),
            ],
        ]
    )


def stable_graph(alpha: float) -> tuple[PchipInterpolator, float, float]:
    """Reconstruct both local stable-manifold branches as a graph D=h(beta)."""
    jacobian = unforced_jacobian(alpha)
    eigenvalues, eigenvectors = np.linalg.eig(jacobian)
    stable_index = int(np.argmin(np.abs(eigenvalues)))
    stable_vector = np.real(eigenvectors[:, stable_index])
    if stable_vector[0] < 0:
        stable_vector *= -1

    saddle = np.array([SADDLE_POLICY, SADDLE_STOCK])

    def inverse_step(target: np.ndarray, guess: float) -> np.ndarray:
        def residual(beta: float) -> float:
            stock = (target[1] - INJECTION) / stock_multiplier(beta)
            return beta + alpha * gradient(beta, stock) - target[0]

        second_guess = guess + (1e-7 if guess < 0.999999 else -1e-7)
        result = root_scalar(
            residual,
            x0=guess,
            x1=second_guess,
            method="secant",
            maxiter=100,
            xtol=1e-14,
        )
        beta = float(result.root)
        stock = float((target[1] - INJECTION) / stock_multiplier(beta))
        return np.array([beta, stock])

    points = [saddle]
    # Interlaced starting scales make the inverse-iteration points dense on a
    # logarithmic distance scale while retaining O(epsilon^2) tangent error.
    for direction in (-1.0, 1.0):
        for epsilon in np.geomspace(1e-13, 3e-8, 31):
            point = saddle + direction * epsilon * stable_vector
            for _ in range(140):
                if not (
                    0.0 < point[0] < 1.0
                    and INJECTION < point[1] < INJECTION / LAMBDA0
                ):
                    break
                points.append(point.copy())
                displacement = point[0] - SADDLE_POLICY
                point = inverse_step(point, point[0] + 0.05 * displacement)

    points_array = np.array(points)
    order = np.argsort(points_array[:, 0])
    points_array = points_array[order]
    # PCHIP requires strictly increasing abscissae.  Round only for duplicate
    # detection; retain the most recently generated full-precision ordinate.
    rounded = np.round(points_array[:, 0], 14)
    _, unique_indices = np.unique(rounded, return_index=True)
    points_array = points_array[np.sort(unique_indices)]
    graph = PchipInterpolator(points_array[:, 0], points_array[:, 1], extrapolate=False)
    return graph, float(points_array[0, 0]), float(points_array[-1, 0])


def natural_seed(alpha: float, horizon: int) -> np.ndarray:
    controls = np.zeros(horizon)
    beta = 0.0
    stock = CALIBRATED_STOCK
    for time in range(horizon):
        drift = float(gradient(beta, stock))
        controls[time] = -2 * drift
        next_beta = np.clip(beta - alpha * drift, 0.0, 1.0)
        next_stock = stock_multiplier(beta) * stock + INJECTION
        beta, stock = float(next_beta), float(next_stock)
    return controls


def crossing_objective(
    alpha: float, controls: np.ndarray, penalty: float
) -> tuple[float, np.ndarray, Orbit]:
    orbit = forward(alpha, controls)
    # Price the literal running-maximum event.  Controls after the maximizing
    # time contribute only their own quadratic gradient and are therefore
    # driven to zero by the optimizer.
    maximum_index = int(np.argmax(orbit.policy))
    error = orbit.policy[maximum_index] - SADDLE_POLICY
    objective = 0.5 * float(controls @ controls) + penalty * error**2
    policy_adjoint = 2 * penalty * error
    stock_adjoint = 0.0
    gradient_controls = np.zeros_like(controls)
    for time in range(maximum_index - 1, -1, -1):
        interior = 0.0 if orbit.clipped[time + 1] else 1.0
        gradient_controls[time] = alpha * interior * policy_adjoint
        next_policy_adjoint = (
            interior
            * (1 - 2 * alpha * C**2 * orbit.stock[time])
            * policy_adjoint
            + stock_multiplier_prime(orbit.policy[time])
            * orbit.stock[time]
            * stock_adjoint
        )
        next_stock_adjoint = (
            alpha
            * interior
            * stock_coefficient(orbit.policy[time])
            * policy_adjoint
            + stock_multiplier(orbit.policy[time]) * stock_adjoint
        )
        policy_adjoint, stock_adjoint = next_policy_adjoint, next_stock_adjoint
    return objective, controls + gradient_controls, orbit


def exit_objective(
    alpha: float,
    controls: np.ndarray,
    penalty: float,
    graph: PchipInterpolator,
    graph_min: float,
    graph_max: float,
) -> tuple[float, np.ndarray, Orbit]:
    orbit = forward(alpha, controls)
    terminal_policy = orbit.policy[-1]
    # Keep the optimization on the reconstructed graph.  The optimum found in
    # every reported run is interior to this interval; this guard is inactive
    # there and exists only to prevent undefined interpolation probes.
    clipped_policy = float(np.clip(terminal_policy, graph_min, graph_max))
    boundary_stock = float(graph(clipped_policy))
    boundary_slope = float(graph.derivative()(clipped_policy))
    manifold_error = orbit.stock[-1] - boundary_stock
    range_error = terminal_policy - clipped_policy
    objective = (
        0.5 * float(controls @ controls)
        + penalty * manifold_error**2
        + penalty * range_error**2
    )
    policy_adjoint = -2 * penalty * manifold_error * boundary_slope
    if range_error != 0.0:
        policy_adjoint += 2 * penalty * range_error
    stock_adjoint = 2 * penalty * manifold_error
    gradient_controls = np.empty_like(controls)
    for time in range(len(controls) - 1, -1, -1):
        interior = 0.0 if orbit.clipped[time + 1] else 1.0
        gradient_controls[time] = alpha * interior * policy_adjoint
        next_policy_adjoint = (
            interior
            * (1 - 2 * alpha * C**2 * orbit.stock[time])
            * policy_adjoint
            + stock_multiplier_prime(orbit.policy[time])
            * orbit.stock[time]
            * stock_adjoint
        )
        next_stock_adjoint = (
            alpha
            * interior
            * stock_coefficient(orbit.policy[time])
            * policy_adjoint
            + stock_multiplier(orbit.policy[time]) * stock_adjoint
        )
        policy_adjoint, stock_adjoint = next_policy_adjoint, next_stock_adjoint
    return objective, controls + gradient_controls, orbit


def optimize(
    alpha: float,
    horizon: int,
    objective,
    seed: np.ndarray,
) -> tuple[np.ndarray, Orbit]:
    controls = seed.copy()
    for penalty in (1e4, 1e6, 1e8, 1e10, 1e12):
        result = minimize(
            lambda vector: objective(vector, penalty)[:2],
            controls,
            jac=True,
            method="L-BFGS-B",
            options={
                "maxiter": 4000,
                "maxfun": 12000,
                "ftol": 1e-20,
                "gtol": 1e-14,
                "maxls": 40,
            },
        )
        controls = result.x
    return controls, objective(controls, 1e12)[2]


def run_rate(alpha: float, horizon: int) -> dict[str, float]:
    graph, graph_min, graph_max = stable_graph(alpha)
    seed = natural_seed(alpha, horizon)

    crossing_controls, crossing_orbit = optimize(
        alpha,
        horizon,
        lambda vector, penalty: crossing_objective(alpha, vector, penalty),
        seed,
    )
    # Use both the natural and the optimized-crossing families.  The latter is
    # important in the focus regime, where its terminal stock lies below the
    # separatrix and the optimizer must price the remaining passage.
    exit_candidates = []
    for exit_seed in (seed, crossing_controls):
        controls, orbit = optimize(
            alpha,
            horizon,
            lambda vector, penalty: exit_objective(
                alpha,
                vector,
                penalty,
                graph,
                graph_min,
                graph_max,
            ),
            exit_seed,
        )
        error = orbit.stock[-1] - float(graph(orbit.policy[-1]))
        exit_candidates.append((0.5 * float(controls @ controls), abs(error), controls, orbit))
    exit_candidates.sort(key=lambda row: (row[1] > 1e-7, row[0]))
    exit_action, exit_error, exit_controls, exit_orbit = exit_candidates[0]

    # The exit solution is itself a crossing seed.  This restart prevents the
    # running-maximum problem from being reported from a higher-action local
    # overshoot family in the focus regime.
    crossing_candidates = [(crossing_controls, crossing_orbit)]
    restarted_controls, restarted_orbit = optimize(
        alpha,
        horizon,
        lambda vector, penalty: crossing_objective(alpha, vector, penalty),
        exit_controls,
    )
    crossing_candidates.append((restarted_controls, restarted_orbit))
    crossing_controls, crossing_orbit = min(
        crossing_candidates,
        key=lambda row: 0.5 * float(row[0] @ row[0]),
    )

    # One more mutual polish is enough to collapse the target-dependent local
    # families at the tested horizons: crossing supplies a low-action approach,
    # and the manifold constraint supplies its vanishing passage correction.
    polished_exit_controls, polished_exit_orbit = optimize(
        alpha,
        horizon,
        lambda vector, penalty: exit_objective(
            alpha,
            vector,
            penalty,
            graph,
            graph_min,
            graph_max,
        ),
        crossing_controls,
    )
    polished_exit_error = abs(
        polished_exit_orbit.stock[-1]
        - float(graph(polished_exit_orbit.policy[-1]))
    )
    polished_exit_action = 0.5 * float(
        polished_exit_controls @ polished_exit_controls
    )
    if polished_exit_error <= 1e-7 and polished_exit_action < exit_action:
        exit_action = polished_exit_action
        exit_error = polished_exit_error
        exit_controls = polished_exit_controls
        exit_orbit = polished_exit_orbit

    polished_crossing_controls, polished_crossing_orbit = optimize(
        alpha,
        horizon,
        lambda vector, penalty: crossing_objective(alpha, vector, penalty),
        exit_controls,
    )
    if 0.5 * float(polished_crossing_controls @ polished_crossing_controls) < (
        0.5 * float(crossing_controls @ crossing_controls)
    ):
        crossing_controls = polished_crossing_controls
        crossing_orbit = polished_crossing_orbit

    reverse = reverse_jacobian(alpha)
    reverse_discriminant = float(np.trace(reverse) ** 2 - 4 * np.linalg.det(reverse))
    crossing_action = 0.5 * float(crossing_controls @ crossing_controls)
    crossing_index = int(np.argmax(crossing_orbit.policy))
    crossing_prefix_action = 0.5 * float(
        crossing_controls[:crossing_index] @ crossing_controls[:crossing_index]
    )
    return {
        "alpha": alpha,
        "horizon": float(horizon),
        "reverse_discriminant": reverse_discriminant,
        "crossing_action": crossing_action,
        "crossing_prefix_action": crossing_prefix_action,
        "crossing_time": float(crossing_index),
        "crossing_policy_error": crossing_orbit.policy[crossing_index] - SADDLE_POLICY,
        "crossing_deficit": float(
            stationary_stock(crossing_orbit.policy[crossing_index])
            - crossing_orbit.stock[crossing_index]
        ),
        "exit_action": exit_action,
        "exit_error": exit_error,
        "exit_policy": float(exit_orbit.policy[-1]),
        "exit_stock": float(exit_orbit.stock[-1]),
        "gap": exit_action - crossing_action,
        "graph_min": graph_min,
        "graph_max": graph_max,
    }


def main() -> None:
    parser = argparse.ArgumentParser()
    parser.add_argument("--quick", action="store_true")
    parser.add_argument(
        "--horizon-check",
        action="store_true",
        help="also reproduce the alpha=0.30 finite-horizon residual check",
    )
    arguments = parser.parse_args()
    if arguments.quick:
        grid = ((0.10, 1400), (0.20, 700), (0.30, 500))
    else:
        grid = (
            (0.10, 1600),
            (0.17, 950),
            (0.173, 900),
            (0.18, 850),
            (0.20, 750),
            (0.25, 600),
            (0.30, 500),
        )
    if arguments.horizon_check:
        grid = tuple(grid) + ((0.30, 350),)
    print(
        f"saddle beta={SADDLE_POLICY:.12f} D={SADDLE_STOCK:.12f}",
        flush=True,
    )
    results = []
    for alpha, horizon in grid:
        result = run_rate(alpha, horizon)
        results.append(result)
        print(
            "alpha={alpha:.6f} T={horizon:.0f} discR={reverse_discriminant:+.8e} "
            "Vx={crossing_action:.10f} t_x={crossing_time:.0f} "
            "theta_x={crossing_deficit:.6e} "
            "V={exit_action:.10f} gap={gap:+.6e} "
            "exit=({exit_policy:.9f},{exit_stock:.9f}) err={exit_error:.2e}".format(
                **result
            ),
            flush=True,
        )
    transition_grid = [
        result for result in results if result["horizon"] >= 500
    ]
    has_real_modes = any(
        result["reverse_discriminant"] >= 0 for result in transition_grid
    )
    has_complex_modes = any(
        result["reverse_discriminant"] < 0 for result in transition_grid
    )
    maximum_residual = max(abs(result["gap"]) for result in transition_grid)
    if not (has_real_modes and has_complex_modes and maximum_residual < 5e-7):
        raise SystemExit(
            "probe failed: expected both spectrum regimes and action residuals below 5e-7"
        )
    print(
        "diagnostic: reverse-spectrum sign changes, while max |V_boundary-Vx| "
        f"is {maximum_residual:.3e}; no strict-gap onset is resolved",
        flush=True,
    )


if __name__ == "__main__":
    main()
