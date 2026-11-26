import math, random
from analyze_552_polarity import build_ER

# Test vertex deletions on ER(q) for q = 5, 7, 8, 9, 11!
# If G' <= ER(q) has N' vertices and min degree d = delta(G'),
# then G' is C4-free and complement has max degree N' - 1 - d < N' - d = n.
# So it witnesses R(C4, S_n) >= N' + 1 = n + d + 1!
# Wait: compare d with ceil(sqrt(n))!
# If d >= ceil(sqrt(n)) - 1, then R(C4, S_n) >= n + ceil(sqrt(n)).
# If d >= ceil(sqrt(n)), then R(C4, S_n) >= n + ceil(sqrt(n)) + 1.

def best_deletion(q, s_list, trials=400, seed=42):
    rng = random.Random(seed)
    pts, adj, is_abs = build_ER(q)
    N = len(pts)
    adj_bits = [0] * N
    for i in range(N):
        m = 0
        for j in adj[i]:
            m |= (1 << j)
        adj_bits[i] = m
    results = []
    for s in s_list:
        N_prime = N - s
        # Strategy 1: greedy/local search maximizing delta(G'), tie-broken by count of min-degree vertices
        best_delta = -1
        # Start from deleting absolute points first if s <= q+1, or random + SA
        for restart in range(15):
            # Initial set S of surviving vertices (size N_prime)
            if restart == 0:
                # delete all abs points first, then non-abs
                abs_idx = [i for i in range(N) if is_abs[i]]
                non_idx = [i for i in range(N) if not is_abs[i]]
                rng.shuffle(abs_idx)
                rng.shuffle(non_idx)
                order = non_idx + abs_idx
                surv = set(order[:N_prime])
            elif restart == 1:
                # keep a neighborhood or delete lines? Let's start with random
                surv = set(rng.sample(range(N), N_prime))
            else:
                surv = set(rng.sample(range(N), N_prime))
            deleted = [i for i in range(N) if i not in surv]
            surv_list = list(surv)
            mask = 0
            for v in surv_list:
                mask |= (1 << v)
            degs = {v: (adj_bits[v] & mask).bit_count() for v in range(N)}
            cur_min = min(degs[v] for v in surv_list)
            cur_min_cnt = sum(1 for v in surv_list if degs[v] == cur_min)
            if cur_min > best_delta:
                best_delta = cur_min
            # Hill climb / SA swaps (swap a min-degree surviving vertex out with a high-degree-into-surv deleted vertex)
            for step in range(trials):
                if s == 0: break
                # pick u in surv with minimal or near-minimal degree
                min_verts = [v for v in surv_list if degs[v] <= cur_min + 1]
                u = rng.choice(min_verts)
                # pick w in deleted with maximal degree into (surv \ {u})
                # quick sample or all if small
                cand_del = deleted if len(deleted) <= 25 else rng.sample(deleted, 25)
                best_w = None
                best_score = (-1, -1)
                mask_u = mask ^ (1 << u)
                for w in cand_del:
                    dw = (adj_bits[w] & mask_u).bit_count()
                    # Check min degree after swap
                    # Wait: fast score: (min_deg_after, -cnt)
                    # Actually compute exact new min deg of surv_list - {u} + {w}
                    # Adjust degs temporarily
                    m_new = mask_u | (1 << w)
                    # neighbors of u lose 1, neighbors of w gain 1
                    # only check min deg
                    min_after = dw
                    cnt_after = 1
                    for v in surv_list:
                        if v == u: continue
                        dv = degs[v] - ((adj_bits[u] >> v) & 1) + ((adj_bits[w] >> v) & 1)
                        if dv < min_after:
                            min_after = dv
                            cnt_after = 1
                        elif dv == min_after:
                            cnt_after += 1
                    sc = (min_after, -cnt_after)
                    if sc > best_score:
                        best_score = sc
                        best_w = w
                if best_score >= (cur_min, -cur_min_cnt) or rng.random() < 0.03:
                    w = best_w
                    # perform swap u <-> w
                    surv.remove(u); surv.add(w)
                    surv_list[surv_list.index(u)] = w
                    deleted[deleted.index(w)] = u
                    mask = mask_u | (1 << w)
                    for v in range(N):
                        degs[v] = (adj_bits[v] & mask).bit_count()
                    cur_min = min(degs[v] for v in surv_list)
                    cur_min_cnt = sum(1 for v in surv_list if degs[v] == cur_min)
                    if cur_min > best_delta:
                        best_delta = cur_min
        n_witness = N_prime - best_delta
        lb_R = N_prime + 1
        target_0 = n_witness + math.ceil(math.sqrt(n_witness))
        results.append((s, N_prime, best_delta, n_witness, lb_R, target_0, lb_R - target_0))
    return results

for q, s_range in [(5, range(0, 12)), (7, range(0, 22)), (8, range(0, 22)), (9, range(0, 25))]:
    print(f"=== ER({q}) deletions ===")
    res = best_deletion(q, s_range, trials=250)
    for s, Np, d, nw, lbR, targ, diff in res:
        print(f"  del s={s:2d} -> N'={Np:2d}, delta>={d:2d} -> n={nw:2d}: R(C4,S_{nw})>={lbR:2d} (n+ceil(sqrt(n))={targ:2d}, diff={diff:+d})")
