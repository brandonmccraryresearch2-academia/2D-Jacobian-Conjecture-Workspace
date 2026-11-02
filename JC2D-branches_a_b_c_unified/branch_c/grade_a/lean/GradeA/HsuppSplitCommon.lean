/- Shared wdeg/qexp for all Hsupp split files. Defined once, here, so
   split files can be imported together without duplicate-name clashes. -/
namespace BranchC.HsuppSplit

def wdeg (t : Nat × Nat × Nat × Nat × Nat) : Nat :=
  t.1 + 2 * t.2.1 + 3 * t.2.2.1 + 3 * t.2.2.2.1 + 4 * t.2.2.2.2

def qexp (t : Nat × Nat × Nat × Nat × Nat) : Nat := t.2.2.2.2

end BranchC.HsuppSplit
