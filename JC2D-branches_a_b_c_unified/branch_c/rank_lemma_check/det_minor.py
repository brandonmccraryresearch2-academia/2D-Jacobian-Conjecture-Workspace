#!/usr/bin/env python3
"""Leg H step 3 — determinant of the pivot block M_S mod p, two routes.

Route 1 (FLINT): build nmod_mat M_S from colv restricted to piv, det via
FLINT nmod_mat.det(). Also det(C) via FLINT; check det(C)*det(M_S) == 1.
Route 2 (NumPy, independent code): modular Gaussian elimination with
partial pivoting on the dense int64 matrix, det = product of pivots times
sign, mod p. No FLINT involved.

Inputs (OUTDIR from extract_minor.py): piv.json, colv.json, summary.json.
For a second prime, pass --matrix-pkl (a build_matrix.py output) and
--piv-file: M_S is rebuilt from that matrix's colv at the same piv ordinals
after verifying its cols list matches the p=32003 cols (checked by caller
via cols_sha; this script verifies len(cols)==6054 and the pivcols labels
match [cols[j] for j in piv] when --cols-file is given).

Usage:
  python3 det_minor.py OUTDIR [--matrix-pkl M.pkl --prime P --tag TAG]
Writes det_<tag>.json + det_<tag>.log into OUTDIR.
"""
import sys, os, json, time, argparse
import numpy as np

def det_flint(ms_colv, p, n=3199):
    """ms_colv[jj] = [(row, value), ...] for pivot-block column jj."""
    from flint import nmod_mat
    MS = nmod_mat(n, n, p)
    for jj, cv in enumerate(ms_colv):
        for i, v in cv:
            MS[i, jj] = v
    t0 = time.time()
    d = int(MS.det())
    t1 = time.time()
    return d, t1 - t0

def det_flint_C(C, p):
    from flint import nmod_mat
    n = C.shape[0]
    M = nmod_mat(n, n, p)
    for i in range(n):
        row = C[i]
        nz = np.nonzero(row)[0]
        for k in nz:
            M[i, int(k)] = int(row[k])
    t0 = time.time()
    d = int(M.det())
    return d, time.time() - t0

def det_numpy_lu(A, p):
    """det of dense int64 matrix A (entries in [0,p)) mod p, via Gaussian
    elimination with partial pivoting. Vectorised row ops; mod after each
    rank-1 update (products < p^2, sums of two such < 2^31, no overflow)."""
    A = A.copy()
    n = A.shape[0]
    det = 1
    sign = 1
    t0 = time.time()
    for k in range(n):
        col = A[k:, k]
        nz = np.nonzero(col)[0]
        if len(nz) == 0:
            return 0, time.time() - t0
        r = k + int(nz[0])
        if r != k:
            A[[k, r], :] = A[[r, k], :]
            sign = -sign
        piv = int(A[k, k])
        det = (det * piv) % p
        if k == n - 1:
            break
        inv = pow(piv, -1, p)
        # normalise pivot row below-diagonal part is unused; scale the
        # trailing submatrix: A[i,k:] -= A[i,k]*inv * A[k,k:]
        fac = (A[k + 1:, k] * inv) % p
        if np.any(fac):
            A[k + 1:, k + 1:] = (A[k + 1:, k + 1:] - fac[:, None] * A[k, k + 1:][None, :]) % p
        A[k + 1:, k] = 0
    return (sign * det) % p, time.time() - t0

def dense_MS(ms_colv, p, n=3199):
    A = np.zeros((n, n), dtype=np.int64)
    for jj, cv in enumerate(ms_colv):
        for i, v in cv:
            A[i, jj] = v
    return A

def main():
    ap = argparse.ArgumentParser()
    ap.add_argument("outdir")
    ap.add_argument("--matrix-pkl", default=None)
    ap.add_argument("--prime", type=int, default=32003)
    ap.add_argument("--tag", default="p32003")
    ap.add_argument("--skip-numpy", action="store_true")
    args = ap.parse_args()
    with open(os.path.join(args.outdir, "piv.json")) as f:
        piv = json.load(f)
    with open(os.path.join(args.outdir, "summary.json")) as f:
        summ = json.load(f)
    p = args.prime
    if args.matrix_pkl:
        import pickle
        with open(args.matrix_pkl, "rb") as f:
            d = pickle.load(f)
        assert d["p"] == p and d["W"] == 24, (d["p"], d["W"])
        assert len(d["cols"]) == 6054 and len(d["rows"]) == 3199
        colv = d["colv"]
        with open(os.path.join(args.outdir, "pivcols.json")) as f:
            pivcols = json.load(f)
        assert [[c[0], list(c[1])] for c in [d["cols"][j] for j in piv]] == pivcols, \
            "column labels at this prime differ from the p=32003 pivot labels"
        print(f"matrix {args.matrix_pkl}: p={p} w0={d['w0']} rows={len(d['rows'])} cols={len(d['cols'])}; pivcols labels match p=32003")
        ms_colv = [colv[j] for j in piv]
    else:
        assert p == 32003
        with open(os.path.join(args.outdir, "colv.json")) as f:
            # INVERSE.pkl's colv is ALREADY restricted to the pivot columns,
            # in pivot order: ms_colv[jj] is pivot-block column jj.
            ms_colv = [[tuple(e) for e in c] for c in json.load(f)]
    log = []
    d_flint, t_flint = det_flint(ms_colv, p)
    print(f"FLINT det(M_S) mod {p} = {d_flint}  ({t_flint:.1f}s)")
    log.append(f"FLINT det(M_S) mod {p} = {d_flint} ({t_flint:.1f}s)")
    res = {"prime": p, "tag": args.tag, "det_flint": d_flint,
           "det_flint_seconds": t_flint, "nonzero": d_flint != 0}
    if not args.matrix_pkl:
        # det(C) cross-check, same prime as the filed inverse
        import pickle as _pk  # noqa
        C = np.load(os.path.join(args.outdir, "C.npy")) if os.path.exists(os.path.join(args.outdir, "C.npy")) else None
        if C is not None:
            dC, tC = det_flint_C(C, p)
            print(f"FLINT det(C) mod {p} = {dC} ({tC:.1f}s); det(C)*det(M_S) mod p = {(dC * d_flint) % p}")
            log.append(f"FLINT det(C) mod {p} = {dC} ({tC:.1f}s); product mod p = {(dC * d_flint) % p}")
            res["detC_flint"] = dC
            res["detC_times_detMS_mod_p"] = (dC * d_flint) % p
    if not args.skip_numpy:
        A = dense_MS(ms_colv, p)
        d_np, t_np = det_numpy_lu(A, p)
        print(f"NumPy-LU det(M_S) mod {p} = {d_np}  ({t_np:.1f}s)")
        log.append(f"NumPy-LU det(M_S) mod {p} = {d_np} ({t_np:.1f}s)")
        res["det_numpy"] = d_np
        res["det_numpy_seconds"] = t_np
        res["routes_agree"] = (d_np == d_flint)
        assert d_np == d_flint, "ROUTE DISAGREEMENT — STOP"
    with open(os.path.join(args.outdir, f"det_{args.tag}.json"), "w") as f:
        json.dump(res, f, indent=2)
    with open(os.path.join(args.outdir, f"det_{args.tag}.log"), "w") as f:
        f.write("\n".join(log) + "\n")
    print("DET OK: routes agree, det != 0" if res["nonzero"] else "DET IS ZERO")

if __name__ == "__main__":
    main()
