"""Own implementation of a finite-gate branching point-process stress model."""
import heapq

import numpy as np
from numba import njit


@njit(cache=True, nogil=True)
def _simulate(rates, cdf, ap_mean, recovery, bin_width, seed, max_events):
    np.random.seed(seed)
    # Columns: accepted total, accepted AP, rejected primary, rejected AP,
    # AP candidates scheduled within gate, AP candidates beyond gate.
    result = np.zeros((rates.size, 6), dtype=np.int64)
    for gate in range(rates.size):
        rate = rates[gate]
        if rate == 0:
            continue
        primary = np.random.exponential(1.0 / rate)
        live_after = 0.0
        pending = [np.inf]
        events = 0
        while True:
            is_ap = pending[0] < primary
            time = pending[0] if is_ap else primary
            if time >= 1.0:
                break
            if is_ap:
                heapq.heappop(pending)
            else:
                primary = time + np.random.exponential(1.0 / rate)
            events += 1
            if events > max_events:
                raise RuntimeError('Event guard exceeded: abort, never truncate')
            if time < live_after:
                result[gate, 3 if is_ap else 2] += 1
                continue
            result[gate, 0] += 1
            if is_ap:
                result[gate, 1] += 1
            live_after = time + recovery
            daughters = np.random.poisson(ap_mean) if ap_mean > 0 else 0
            for _ in range(daughters):
                index = np.searchsorted(cdf, np.random.random(), side='right')
                delay = (index + np.random.random()) * bin_width
                arrival = live_after + delay
                if arrival < 1.0:
                    heapq.heappush(pending, arrival)
                    result[gate, 4] += 1
                else:
                    result[gate, 5] += 1
    return result


def simulate(rates, cdf, ap_mean, recovery=0.0, bin_width=0.0, seed=0, max_events=100000):
    rates = np.asarray(rates, dtype=np.float64)
    cdf = np.asarray(cdf, dtype=np.float64)
    if rates.ndim != 1 or not np.isfinite(rates).all() or np.any(rates < 0):
        raise ValueError('Rates must be a finite nonnegative vector')
    if cdf.ndim != 1 or not len(cdf) or not np.isfinite(cdf).all():
        raise ValueError('Invalid delay CDF')
    if cdf[0] < 0 or cdf[-1] != 1 or np.any(np.diff(cdf) < 0):
        raise ValueError('Delay CDF must increase to exactly one')
    if not (np.isfinite(ap_mean) and 0 <= ap_mean < 1):
        raise ValueError('Require a subcritical nonnegative offspring mean')
    if not (np.isfinite(recovery) and recovery >= 0 and np.isfinite(bin_width) and bin_width >= 0):
        raise ValueError('Invalid time scales')
    if max_events < 1 or not 0 <= seed < 2**32:
        raise ValueError('Invalid guard or seed')
    return _simulate(rates, cdf, ap_mean, recovery, bin_width, seed, max_events)
