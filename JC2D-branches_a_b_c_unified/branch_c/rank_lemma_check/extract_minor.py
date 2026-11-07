#!/usr/bin/env python3
"""Leg H step 2 — inspect INVERSE.pkl WITHOUT executing arbitrary pickle code.

Stage 1: pickletools.genops over the file; list every GLOBAL/STACK_GLOBAL
opcode (i.e. every class the pickle references) and the top-level structure.
Stage 2: restricted unpickling allowing ONLY the classes make_inverse.py
writes: builtins containers/scalars + numpy ndarray/dtype reconstruct.
Any other GLOBAL aborts the load.

Usage: python3 extract_minor.py INVERSE.pkl OUTDIR
Writes: globals.txt, summary.json, piv.json, pivcols.json, colv.json,
c_stats.json. Exits nonzero on any mismatch.
"""
import sys, os, json, hashlib, pickle, pickletools, io

ALLOWED = {
    ("builtins", "list"), ("builtins", "dict"), ("builtins", "tuple"),
    ("builtins", "set"), ("builtins", "frozenset"),
    ("builtins", "int"), ("builtins", "float"), ("builtins", "str"),
    ("builtins", "bool"), ("builtins", "complex"), ("builtins", "bytes"),
    ("builtins", "bytearray"), ("builtins", "slice"), ("builtins", "range"),
    ("numpy", "ndarray"), ("numpy", "dtype"),
    ("numpy.core.multiarray", "_reconstruct"),
    ("numpy._core.multiarray", "_reconstruct"),
    ("numpy.core.multiarray", "scalar"),
    ("numpy._core.multiarray", "scalar"),
    ("numpy.dtypes", "Int64DType"), ("numpy.dtypes", "Float64DType"),
    ("numpy", "int64"), ("numpy", "float64"),
    ("codecs", "encode"),
    ("copyreg", "_reconstructor"), ("copyreg", "__newobj__"),
    ("__builtin__", "list"), ("__builtin__", "dict"),
}

class RestrictedUnpickler(pickle.Unpickler):
    def find_class(self, module, name):
        if (module, name) in ALLOWED:
            return super().find_class(module, name)
        raise pickle.UnpicklingError(f"FORBIDDEN global {module}.{name}")

def main():
    pkl, outdir = sys.argv[1], sys.argv[2]
    os.makedirs(outdir, exist_ok=True)
    data = open(pkl, "rb").read()
    print(f"file bytes: {len(data)}")
    print(f"file sha256: {hashlib.sha256(data).hexdigest()}")
    # Stage 1: opcode scan
    globals_seen = []
    opcodes = []
    with open(pkl, "rb") as f:
        for op, arg, pos in pickletools.genops(f):
            opcodes.append(op.name)
            if op.name in ("GLOBAL", "STACK_GLOBAL"):
                globals_seen.append(arg)
    with open(os.path.join(outdir, "globals.txt"), "w") as f:
        f.write("GLOBAL/STACK_GLOBAL references in INVERSE.pkl:\n")
        for g in sorted(set(globals_seen)):
            f.write(f"  {g}\n")
        f.write(f"\nTotal opcodes: {len(opcodes)}\n")
        f.write(f"First opcode: {opcodes[0] if opcodes else None}; last: {opcodes[-1] if opcodes else None}\n")
    print("globals referenced:")
    for g in sorted(set(globals_seen)):
        print(f"  {g}")
    # Stage 2: restricted load
    with open(pkl, "rb") as f:
        d = RestrictedUnpickler(f).load()
    assert isinstance(d, dict), type(d)
    print(f"top-level keys: {sorted(d.keys())}")
    assert sorted(d.keys()) == ["C", "colv", "p", "piv", "pivcols"], sorted(d.keys())
    p, piv, pivcols, colv, C = d["p"], d["piv"], d["pivcols"], d["colv"], d["C"]
    assert p == 32003, p
    assert len(piv) == 3199, len(piv)
    assert len(set(piv)) == 3199, "pivot indices not distinct"
    assert min(piv) >= 0 and max(piv) <= 6053, (min(piv), max(piv))
    assert len(pivcols) == 3199 and len(colv) == 3199
    import numpy as np
    assert isinstance(C, np.ndarray) and C.shape == (3199, 3199), (type(C), getattr(C, "shape", None))
    assert str(C.dtype) == "int64", C.dtype
    assert int(C.min()) >= 0 and int(C.max()) < p, (int(C.min()), int(C.max()))
    piv_hash = hashlib.sha256(repr(piv).encode()).hexdigest()[:16]
    c_hash = hashlib.sha256(C.tobytes()).hexdigest()[:16]
    print(f"sha256(repr(piv))[:16] = {piv_hash}  (filed: 00e40995b010f30a)")
    print(f"sha256(C.tobytes())[:16] = {c_hash}  (filed: 6cffa0100555b7b8)")
    assert piv_hash == "00e40995b010f30a", "PIVOT LIST HASH MISMATCH — STOP"
    assert c_hash == "6cffa0100555b7b8", "C HASH MISMATCH — STOP"
    nnz_c = int(np.count_nonzero(C))
    sup = [len(c) for c in colv]
    summary = {
        "file_bytes": len(data),
        "file_sha256": hashlib.sha256(data).hexdigest(),
        "p": p, "n_pivots": len(piv),
        "piv_min": min(piv), "piv_max": max(piv),
        "piv_sorted": piv == sorted(piv),
        "piv_sha256_repr_16": piv_hash,
        "C_shape": list(C.shape), "C_dtype": str(C.dtype),
        "C_nonzero": nnz_c, "C_total": 3199 * 3199,
        "C_nonzero_frac": nnz_c / (3199 * 3199),
        "C_sha256_bytes_16": c_hash,
        "C_min": int(C.min()), "C_max": int(C.max()),
        "MS_nnz": sum(sup), "MS_col_support_min": min(sup),
        "MS_col_support_max": max(sup),
        "pivcols_generators": {g: sum(1 for pc in pivcols if pc[0] == g) for g in sorted({pc[0] for pc in pivcols})},
    }
    with open(os.path.join(outdir, "summary.json"), "w") as f:
        json.dump(summary, f, indent=2)
    with open(os.path.join(outdir, "piv.json"), "w") as f:
        json.dump(piv, f)
    with open(os.path.join(outdir, "pivcols.json"), "w") as f:
        json.dump([[pc[0], list(pc[1])] for pc in pivcols], f)
    with open(os.path.join(outdir, "colv.json"), "w") as f:
        json.dump([[list(e) for e in c] for c in colv], f)
    np.save(os.path.join(outdir, "C.npy"), C)
    print(json.dumps(summary, indent=2))
    print("EXTRACTION OK")

if __name__ == "__main__":
    main()
