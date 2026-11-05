import Mathlib

/-!
# `R` modulo 109: Bézout certificates for irreducibility

`R = X⁵ − X⁴ + 3X³ + 3X² + 26` over `𝔽₁₀₉`. Irreducibility is certified by two gcd computations against
`X^(109^i) − X` (the "two gcds" approach), each witnessed by an explicit Bézout identity:

* **Linear** (`i = 1`): `u1 * R + v1 * (X^109 - X) = 1`, so `gcd(R, X^109 - X) = 1`: `R` has no root in `𝔽₁₀₉`.
* **Quadratic** (`i = 2`): direct Bézout for `X^(109²) - X` would need a degree-11880 cofactor. Instead we use a
  modular reduction: `T = X^(109²) mod R` (computed externally), `S = T - X`, and
  - `bezout_quad_small : aq * R + bq * S = 1` (all factors of degree < 5),
  - `quad_mod : (X^(109²) - X) % R = S` (single polynomial remainder),
  from which `IsCoprime R (X^(109²) - X)` follows algebraically (see `IrreducibleR109.lean`).

Verification mechanism (NOT `decide`: the 109-term linear certificate times out under `decide`,
and polynomial `decide` fails on these sizes):
* Bézout identities are proved over `ℤ[X]` by `unfold` + `ring` (identities hold up to multiples of 109),
  then reduced mod 109 through `red` (the `109`-vanishing trick).
* `quad_mod` is proved by a Frobenius computation: `X^109 = Q * R + A` over `ℤ[X]`, reduction of the
  face polynomial `A` by `add_pow_char`, and the key divisibility lemma.
All certificates were computed externally (Python/flint `xgcd` over `𝔽₁₀₉`) and are *verified* here
by the proofs below. The general deterministic factorization algorithm (OpenAI catalog family 142)
is not used: its exponent-1012 complexity bound is vast overkill for a degree-5 polynomial, where
these two explicit Bézout identities are the complete certificate.
-/

open Polynomial

set_option maxHeartbeats 4000000
set_option maxRecDepth 10000

namespace BranchC.GradeA

instance fact_prime_109 : Fact (Nat.Prime 109) := ⟨by norm_num⟩



/-! ### F109 defs -/

noncomputable def R109 : (ZMod 109)[X] := X ^ 5 - X ^ 4 + 3 * X ^ 3 + 3 * X ^ 2 + 26

noncomputable def u1 : (ZMod 109)[X] := C (21 : ZMod 109) + C (85 : ZMod 109) * X + C (29 : ZMod 109) * X^2 + C (56 : ZMod 109) * X^3 + C (19 : ZMod 109) * X^4 + C (59 : ZMod 109) * X^5 + C (94 : ZMod 109) * X^6 + C (13 : ZMod 109) * X^7 + C (48 : ZMod 109) * X^8 + C (94 : ZMod 109) * X^9 + C (53 : ZMod 109) * X^10 + C (35 : ZMod 109) * X^11 + C (85 : ZMod 109) * X^12 + C (81 : ZMod 109) * X^14 + C (44 : ZMod 109) * X^15 + C (89 : ZMod 109) * X^16 + C (41 : ZMod 109) * X^17 + C (80 : ZMod 109) * X^18 + C (80 : ZMod 109) * X^19 + C (80 : ZMod 109) * X^20 + C (30 : ZMod 109) * X^21 + C (4 : ZMod 109) * X^22 + C (46 : ZMod 109) * X^23 + C (38 : ZMod 109) * X^24 + C (51 : ZMod 109) * X^25 + C (48 : ZMod 109) * X^26 + C (71 : ZMod 109) * X^27 + C (26 : ZMod 109) * X^28 + C (79 : ZMod 109) * X^29 + C (39 : ZMod 109) * X^30 + C (81 : ZMod 109) * X^31 + C (14 : ZMod 109) * X^32 + C (93 : ZMod 109) * X^33 + C (42 : ZMod 109) * X^34 + C (27 : ZMod 109) * X^35 + C (7 : ZMod 109) * X^36 + C (37 : ZMod 109) * X^37 + C (57 : ZMod 109) * X^38 + C (74 : ZMod 109) * X^39 + C (89 : ZMod 109) * X^40 + C (7 : ZMod 109) * X^41 + C (70 : ZMod 109) * X^42 + C (86 : ZMod 109) * X^43 + C (42 : ZMod 109) * X^44 + C (4 : ZMod 109) * X^45 + C (17 : ZMod 109) * X^46 + C (54 : ZMod 109) * X^47 + C (42 : ZMod 109) * X^48 + C (70 : ZMod 109) * X^49 + C (2 : ZMod 109) * X^50 + C (43 : ZMod 109) * X^51 + C (8 : ZMod 109) * X^52 + C (42 : ZMod 109) * X^53 + C (46 : ZMod 109) * X^54 + C (43 : ZMod 109) * X^56 + C (105 : ZMod 109) * X^57 + C (100 : ZMod 109) * X^58 + C (65 : ZMod 109) * X^59 + C (87 : ZMod 109) * X^60 + C (63 : ZMod 109) * X^61 + C (20 : ZMod 109) * X^62 + C (61 : ZMod 109) * X^63 + C (29 : ZMod 109) * X^64 + C (61 : ZMod 109) * X^65 + C (76 : ZMod 109) * X^66 + C (96 : ZMod 109) * X^67 + C (71 : ZMod 109) * X^68 + C (82 : ZMod 109) * X^69 + C (40 : ZMod 109) * X^70 + C (46 : ZMod 109) * X^71 + C (73 : ZMod 109) * X^72 + C (45 : ZMod 109) * X^73 + C (14 : ZMod 109) * X^74 + C (104 : ZMod 109) * X^75 + C (11 : ZMod 109) * X^76 + C (44 : ZMod 109) * X^77 + C (61 : ZMod 109) * X^78 + C (60 : ZMod 109) * X^79 + C (43 : ZMod 109) * X^80 + C (46 : ZMod 109) * X^81 + C (81 : ZMod 109) * X^82 + C (40 : ZMod 109) * X^83 + C (35 : ZMod 109) * X^84 + C (70 : ZMod 109) * X^85 + C (43 : ZMod 109) * X^86 + C (45 : ZMod 109) * X^87 + C (79 : ZMod 109) * X^88 + C (96 : ZMod 109) * X^89 + C (14 : ZMod 109) * X^90 + C (26 : ZMod 109) * X^91 + C (106 : ZMod 109) * X^92 + C (17 : ZMod 109) * X^93 + C (99 : ZMod 109) * X^94 + C (24 : ZMod 109) * X^95 + C (40 : ZMod 109) * X^96 + C (83 : ZMod 109) * X^97 + C (88 : ZMod 109) * X^98 + C (50 : ZMod 109) * X^99 + C (27 : ZMod 109) * X^100 + C (57 : ZMod 109) * X^101 + C (50 : ZMod 109) * X^102 + C (14 : ZMod 109) * X^103 + C (79 : ZMod 109) * X^104 + C (86 : ZMod 109) * X^105 + C (98 : ZMod 109) * X^106 + C (76 : ZMod 109) * X^107 + C (19 : ZMod 109) * X^108


noncomputable def v1 : (ZMod 109)[X] := C (30 : ZMod 109) + C (54 : ZMod 109) * X + C (30 : ZMod 109) * X^2 + C (52 : ZMod 109) * X^3 + C (90 : ZMod 109) * X^4


noncomputable def T109 : (ZMod 109)[X] := C (17 : ZMod 109) + C (102 : ZMod 109) * X + C (87 : ZMod 109) * X^2 + C (6 : ZMod 109) * X^3 + C (17 : ZMod 109) * X^4

noncomputable def S109 : (ZMod 109)[X] := C (17 : ZMod 109) + C (101 : ZMod 109) * X + C (87 : ZMod 109) * X^2 + C (6 : ZMod 109) * X^3 + C (17 : ZMod 109) * X^4

noncomputable def aq : (ZMod 109)[X] := C (8 : ZMod 109) + C (32 : ZMod 109) * X + C (96 : ZMod 109) * X^2 + C (95 : ZMod 109) * X^3


noncomputable def bq : (ZMod 109)[X] := C (84 : ZMod 109) + C (106 : ZMod 109) * X + C (36 : ZMod 109) * X^2 + C (17 : ZMod 109) * X^3 + C (97 : ZMod 109) * X^4


noncomputable def A : (ZMod 109)[X] := C (33 : ZMod 109) + C (100 : ZMod 109) * X + C (87 : ZMod 109) * X^2 + C (56 : ZMod 109) * X^3 + C (37 : ZMod 109) * X^4

noncomputable def Q : (ZMod 109)[X] := C (70 : ZMod 109) + C (80 : ZMod 109) * X + C (85 : ZMod 109) * X^2 + C (56 : ZMod 109) * X^3 + C (108 : ZMod 109) * X^4 + C (47 : ZMod 109) * X^5 + C (19 : ZMod 109) * X^6 + C (90 : ZMod 109) * X^7 + C (95 : ZMod 109) * X^8 + C (27 : ZMod 109) * X^9 + C (74 : ZMod 109) * X^10 + C (18 : ZMod 109) * X^11 + C (64 : ZMod 109) * X^12 + C (79 : ZMod 109) * X^13 + C (72 : ZMod 109) * X^14 + C (61 : ZMod 109) * X^15 + C (64 : ZMod 109) * X^16 + C (2 : ZMod 109) * X^17 + C (44 : ZMod 109) * X^18 + C (80 : ZMod 109) * X^19 + C (108 : ZMod 109) * X^20 + C (42 : ZMod 109) * X^21 + C (47 : ZMod 109) * X^22 + C (26 : ZMod 109) * X^23 + C (104 : ZMod 109) * X^24 + C (10 : ZMod 109) * X^25 + C (90 : ZMod 109) * X^26 + C (7 : ZMod 109) * X^27 + C (25 : ZMod 109) * X^28 + C (90 : ZMod 109) * X^29 + C (100 : ZMod 109) * X^30 + C (59 : ZMod 109) * X^31 + C (71 : ZMod 109) * X^32 + C (68 : ZMod 109) * X^33 + C (86 : ZMod 109) * X^34 + C (83 : ZMod 109) * X^35 + C (33 : ZMod 109) * X^36 + C (81 : ZMod 109) * X^37 + C (46 : ZMod 109) * X^38 + C (58 : ZMod 109) * X^39 + C (105 : ZMod 109) * X^40 + C (15 : ZMod 109) * X^41 + C (5 : ZMod 109) * X^42 + C (104 : ZMod 109) * X^43 + C (54 : ZMod 109) * X^44 + C (72 : ZMod 109) * X^45 + C (82 : ZMod 109) * X^46 + C (27 : ZMod 109) * X^47 + C (39 : ZMod 109) * X^48 + C (51 : ZMod 109) * X^49 + C (85 : ZMod 109) * X^50 + C (42 : ZMod 109) * X^51 + C (77 : ZMod 109) * X^52 + C (99 : ZMod 109) * X^53 + C (84 : ZMod 109) * X^54 + C (108 : ZMod 109) * X^55 + C (106 : ZMod 109) * X^56 + C (29 : ZMod 109) * X^57 + C (46 : ZMod 109) * X^58 + C (65 : ZMod 109) * X^59 + C (29 : ZMod 109) * X^60 + C (1 : ZMod 109) * X^61 + C (103 : ZMod 109) * X^62 + C (35 : ZMod 109) * X^63 + C (104 : ZMod 109) * X^64 + C (92 : ZMod 109) * X^65 + C (34 : ZMod 109) * X^66 + C (67 : ZMod 109) * X^67 + C (51 : ZMod 109) * X^68 + C (34 : ZMod 109) * X^69 + C (68 : ZMod 109) * X^70 + C (25 : ZMod 109) * X^71 + C (105 : ZMod 109) * X^72 + C (106 : ZMod 109) * X^73 + C (45 : ZMod 109) * X^74 + C (83 : ZMod 109) * X^75 + C (15 : ZMod 109) * X^76 + C (23 : ZMod 109) * X^77 + C (66 : ZMod 109) * X^78 + C (39 : ZMod 109) * X^79 + C (50 : ZMod 109) * X^80 + C (93 : ZMod 109) * X^81 + C (92 : ZMod 109) * X^82 + C (16 : ZMod 109) * X^83 + C (21 : ZMod 109) * X^84 + C (94 : ZMod 109) * X^85 + C (46 : ZMod 109) * X^86 + C (97 : ZMod 109) * X^87 + C (5 : ZMod 109) * X^88 + C (45 : ZMod 109) * X^89 + C (87 : ZMod 109) * X^90 + C (101 : ZMod 109) * X^91 + C (107 : ZMod 109) * X^92 + C (5 : ZMod 109) * X^93 + C (95 : ZMod 109) * X^94 + C (105 : ZMod 109) * X^95 + C (39 : ZMod 109) * X^96 + C (82 : ZMod 109) * X^97 + C (12 : ZMod 109) * X^98 + C (108 : ZMod 109) * X^99 + C (104 : ZMod 109) * X^100 + C (101 : ZMod 109) * X^101 + C (107 : ZMod 109) * X^102 + C (1 : ZMod 109) * X^103 + C (1 : ZMod 109) * X^104

noncomputable def Q2 : (ZMod 109)[X] := C (21 : ZMod 109) + C (58 : ZMod 109) * X + C (91 : ZMod 109) * X^2 + C (78 : ZMod 109) * X^3 + C (24 : ZMod 109) * X^4 + C (62 : ZMod 109) * X^5 + C (102 : ZMod 109) * X^6 + C (99 : ZMod 109) * X^7 + C (98 : ZMod 109) * X^8 + C (62 : ZMod 109) * X^9 + C (100 : ZMod 109) * X^10 + C (10 : ZMod 109) * X^11

noncomputable def red : ℤ[X] →+* (ZMod 109)[X] := Polynomial.mapRingHom (Int.castRingHom (ZMod 109))



/-! ### Z lifts -/

noncomputable def Rint109 : ℤ[X] := X ^ 5 - X ^ 4 + 3 * X ^ 3 + 3 * X ^ 2 + 26

noncomputable def u1Z : ℤ[X] := 21 + 85 * X + 29 * X^2 + 56 * X^3 + 19 * X^4 + 59 * X^5 + 94 * X^6 + 13 * X^7 + 48 * X^8 + 94 * X^9 + 53 * X^10 + 35 * X^11 + 85 * X^12 + 81 * X^14 + 44 * X^15 + 89 * X^16 + 41 * X^17 + 80 * X^18 + 80 * X^19 + 80 * X^20 + 30 * X^21 + 4 * X^22 + 46 * X^23 + 38 * X^24 + 51 * X^25 + 48 * X^26 + 71 * X^27 + 26 * X^28 + 79 * X^29 + 39 * X^30 + 81 * X^31 + 14 * X^32 + 93 * X^33 + 42 * X^34 + 27 * X^35 + 7 * X^36 + 37 * X^37 + 57 * X^38 + 74 * X^39 + 89 * X^40 + 7 * X^41 + 70 * X^42 + 86 * X^43 + 42 * X^44 + 4 * X^45 + 17 * X^46 + 54 * X^47 + 42 * X^48 + 70 * X^49 + 2 * X^50 + 43 * X^51 + 8 * X^52 + 42 * X^53 + 46 * X^54 + 43 * X^56 + 105 * X^57 + 100 * X^58 + 65 * X^59 + 87 * X^60 + 63 * X^61 + 20 * X^62 + 61 * X^63 + 29 * X^64 + 61 * X^65 + 76 * X^66 + 96 * X^67 + 71 * X^68 + 82 * X^69 + 40 * X^70 + 46 * X^71 + 73 * X^72 + 45 * X^73 + 14 * X^74 + 104 * X^75 + 11 * X^76 + 44 * X^77 + 61 * X^78 + 60 * X^79 + 43 * X^80 + 46 * X^81 + 81 * X^82 + 40 * X^83 + 35 * X^84 + 70 * X^85 + 43 * X^86 + 45 * X^87 + 79 * X^88 + 96 * X^89 + 14 * X^90 + 26 * X^91 + 106 * X^92 + 17 * X^93 + 99 * X^94 + 24 * X^95 + 40 * X^96 + 83 * X^97 + 88 * X^98 + 50 * X^99 + 27 * X^100 + 57 * X^101 + 50 * X^102 + 14 * X^103 + 79 * X^104 + 86 * X^105 + 98 * X^106 + 76 * X^107 + 19 * X^108

noncomputable def v1Z : ℤ[X] := 30 + 54 * X + 30 * X^2 + 52 * X^3 + 90 * X^4

noncomputable def aqZ : ℤ[X] := 8 + 32 * X + 96 * X^2 + 95 * X^3

noncomputable def bqZ : ℤ[X] := 84 + 106 * X + 36 * X^2 + 17 * X^3 + 97 * X^4

noncomputable def S109Z : ℤ[X] := 17 + 101 * X + 87 * X^2 + 6 * X^3 + 17 * X^4

noncomputable def W_lin : ℤ[X] := 5 + 20 * X + 7 * X^2 + 16 * X^3 + 7 * X^4 + 15 * X^5 + 25 * X^6 + 5 * X^7 + 16 * X^8 + 25 * X^9 + 14 * X^10 + 13 * X^11 + 24 * X^12 + 2 * X^13 + 23 * X^14 + 13 * X^15 + 23 * X^16 + 14 * X^17 + 22 * X^18 + 23 * X^19 + 22 * X^20 + 12 * X^21 + 5 * X^22 + 14 * X^23 + 10 * X^24 + 14 * X^25 + 14 * X^26 + 19 * X^27 + 9 * X^28 + 22 * X^29 + 12 * X^30 + 22 * X^31 + 7 * X^32 + 25 * X^33 + 13 * X^34 + 9 * X^35 + 6 * X^36 + 10 * X^37 + 15 * X^38 + 19 * X^39 + 24 * X^40 + 5 * X^41 + 21 * X^42 + 23 * X^43 + 12 * X^44 + 6 * X^45 + 7 * X^46 + 14 * X^47 + 11 * X^48 + 19 * X^49 + 3 * X^50 + 13 * X^51 + 4 * X^52 + 11 * X^53 + 13 * X^54 + 1 * X^55 + 13 * X^56 + 26 * X^57 + 25 * X^58 + 20 * X^59 + 26 * X^60 + 19 * X^61 + 9 * X^62 + 19 * X^63 + 9 * X^64 + 17 * X^65 + 21 * X^66 + 25 * X^67 + 21 * X^68 + 24 * X^69 + 14 * X^70 + 15 * X^71 + 21 * X^72 + 13 * X^73 + 7 * X^74 + 28 * X^75 + 4 * X^76 + 14 * X^77 + 18 * X^78 + 15 * X^79 + 14 * X^80 + 14 * X^81 + 22 * X^82 + 12 * X^83 + 12 * X^84 + 20 * X^85 + 12 * X^86 + 14 * X^87 + 22 * X^88 + 25 * X^89 + 7 * X^90 + 11 * X^91 + 28 * X^92 + 5 * X^93 + 28 * X^94 + 9 * X^95 + 12 * X^96 + 24 * X^97 + 22 * X^98 + 16 * X^99 + 11 * X^100 + 17 * X^101 + 14 * X^102 + 6 * X^103 + 22 * X^104 + 22 * X^105 + 26 * X^106 + 23 * X^107 + 9 * X^108 + 5 * X^109 + 3 * X^110 + 1 * X^111 + 1 * X^112 + 1 * X^113

noncomputable def W_quad : ℤ[X] := 15 + 102 * X + 194 * X^2 + 149 * X^3 + 82 * X^4 + 127 * X^5 + 86 * X^6 + 8 * X^7 + 16 * X^8


noncomputable def Apr : ℤ[X] := 33 + 100 * X + 87 * X^2 + 56 * X^3 + 37 * X^4

noncomputable def Q_Z : ℤ[X] := -567308037114557540729697586065135 + -579841502146188888831899514687326 * X + -247417314971400268315483477405924 * X^2 + -28291012675001588880170321596961 * X^3 + 38205574883582326097657885121851 * X^4 + 31330442996445162441721518014864 * X^5 + 11641557713424861879382821027182 * X^6 + 404548025242931300660574861493 * X^7 + -2400746714270236845595569631051 * X^8 + -1654363427043867046002559798962 * X^9 + -526934200613014766443604333808 * X^10 + 35704643683091580618159312475 * X^11 + 143792236286826049657013380991 * X^12 + 85387383000620744502667111388 * X^13 + 22651484096965361105132207106 * X^14 + -4803846675624385977587608879 * X^15 + -8308808026500917222482457191 * X^16 + -4305683290393393482191540934 * X^17 + -899920569126133607589411772 * X^18 + 399543968388199424280853015 * X^19 + 465840393372386539401846531 * X^20 + 211702097627743318854484328 * X^21 + 31138832153288537829001174 * X^22 + -28198574441771405496104915 * X^23 + -25470244783034940574210115 * X^24 + -10113810341507485290232730 * X^25 + -752184915385990108251464 * X^26 + 1823644568406435933393171 * X^27 + 1358704439592957350667207 * X^28 + 467002133941004531098164 * X^29 + -7131599918334025776918 * X^30 + -111588086031133061678903 * X^31 + -70944297341595773026527 * X^32 + -20597817223213521430830 * X^33 + 2825516009955690278508 * X^34 + 6544994522370340287311 * X^35 + 3613872781896568542667 * X^36 + 855190327746313842240 * X^37 + -271279564601212106946 * X^38 + -372604262173615274843 * X^39 + -180109770381118344251 * X^40 + -31808883608683559810 * X^41 + 20448930973718265696 * X^42 + 20555048630653944011 * X^43 + 8714398065284338959 * X^44 + 972651844589159820 * X^45 + -1367327904054347054 * X^46 + -1113655079718646847 * X^47 + -409870091806693975 * X^48 + -11492202668315286 * X^49 + 85792144843558292 * X^50 + 58375373375412615 * X^51 + 18495583130239379 * X^52 + -1312487135328232 * X^53 + -5128020077118554 * X^54 + -3037156132803043 * X^55 + -790702638762803 * X^56 + 180286860161430 * X^57 + 294924745111816 * X^58 + 150850433850755 * X^59 + 31569949162327 * X^60 + -14089847613980 * X^61 + -16639356311110 * X^62 + -7558254457927 * X^63 + -1042033573583 * X^64 + 1035885981954 * X^65 + 894282899900 * X^66 + 349982485695 * X^67 + 27912086107 * X^68 + -63649100048 * X^69 + -49049492210 * X^70 + -16811129707 * X^71 + 616360661 * X^72 + 4077718446 * X^73 + 2430150576 * X^74 + 698312507 * X^75 + -80619873 * X^76 + -227847364 * X^77 + -134640222 * X^78 + -31016783 * X^79 + 11866553 * X^80 + 13451674 * X^81 + 5794532 * X^82 + 1064183 * X^83 + -571357 * X^84 + -730424 * X^85 + -351370 * X^86 + -31731 * X^87 + 61917 * X^88 + 38086 * X^89 + 11096 * X^90 + 755 * X^91 + -2073 * X^92 + -2284 * X^93 + -886 * X^94 + 105 * X^95 + 257 * X^96 + 82 * X^97 + 12 * X^98 + -1 * X^99 + -5 * X^100 + -8 * X^101 + -2 * X^102 + 1 * X^103 + 1 * X^104

noncomputable def A_Z : ℤ[X] := 14750008964978496058972137237693510 + 15075879055800911109629387381870476 * X + 8134774300600079598391663170749429 * X^2 + 4177014947332280599569219663778369 * X^3 + 921123467265069452173346377046489 * X^4

noncomputable def Q2_Z : ℤ[X] := 1218753575270 + 332831899652 * X + -63644321431 * X^2 + -117269782943 * X^3 + -60798798890 * X^4 + -11790217980 * X^5 + 7244854597 * X^6 + 8557331769 * X^7 + 4883633700 * X^8 + 1886419026 * X^9 + 489156021 * X^10 + 69343957 * X^11

noncomputable def T_Z : ℤ[X] := -31687546967395 + -8653078643952 * X + -1998555328714 * X^2 + -1596189081328 * X^3 + 2013400032278 * X^4

noncomputable def Q_Z' : ℤ[X] := 70 + 80 * X + 85 * X^2 + 56 * X^3 + 108 * X^4 + 47 * X^5 + 19 * X^6 + 90 * X^7 + 95 * X^8 + 27 * X^9 + 74 * X^10 + 18 * X^11 + 64 * X^12 + 79 * X^13 + 72 * X^14 + 61 * X^15 + 64 * X^16 + 2 * X^17 + 44 * X^18 + 80 * X^19 + 108 * X^20 + 42 * X^21 + 47 * X^22 + 26 * X^23 + 104 * X^24 + 10 * X^25 + 90 * X^26 + 7 * X^27 + 25 * X^28 + 90 * X^29 + 100 * X^30 + 59 * X^31 + 71 * X^32 + 68 * X^33 + 86 * X^34 + 83 * X^35 + 33 * X^36 + 81 * X^37 + 46 * X^38 + 58 * X^39 + 105 * X^40 + 15 * X^41 + 5 * X^42 + 104 * X^43 + 54 * X^44 + 72 * X^45 + 82 * X^46 + 27 * X^47 + 39 * X^48 + 51 * X^49 + 85 * X^50 + 42 * X^51 + 77 * X^52 + 99 * X^53 + 84 * X^54 + 108 * X^55 + 106 * X^56 + 29 * X^57 + 46 * X^58 + 65 * X^59 + 29 * X^60 + 1 * X^61 + 103 * X^62 + 35 * X^63 + 104 * X^64 + 92 * X^65 + 34 * X^66 + 67 * X^67 + 51 * X^68 + 34 * X^69 + 68 * X^70 + 25 * X^71 + 105 * X^72 + 106 * X^73 + 45 * X^74 + 83 * X^75 + 15 * X^76 + 23 * X^77 + 66 * X^78 + 39 * X^79 + 50 * X^80 + 93 * X^81 + 92 * X^82 + 16 * X^83 + 21 * X^84 + 94 * X^85 + 46 * X^86 + 97 * X^87 + 5 * X^88 + 45 * X^89 + 87 * X^90 + 101 * X^91 + 107 * X^92 + 5 * X^93 + 95 * X^94 + 105 * X^95 + 39 * X^96 + 82 * X^97 + 12 * X^98 + 108 * X^99 + 104 * X^100 + 101 * X^101 + 107 * X^102 + 1 * X^103 + 1 * X^104

noncomputable def Q2_Z' : ℤ[X] := 21 + 58 * X + 91 * X^2 + 78 * X^3 + 24 * X^4 + 62 * X^5 + 102 * X^6 + 99 * X^7 + 98 * X^8 + 62 * X^9 + 100 * X^10 + 10 * X^11

noncomputable def T_Z' : ℤ[X] := 17 + 102 * X + 87 * X^2 + 6 * X^3 + 17 * X^4

noncomputable def S_Z' : ℤ[X] := 17 + 101 * X + 87 * X^2 + 6 * X^3 + 17 * X^4

noncomputable def W_Q : ℤ[X] := -5204660890959243492933005376745 + -5319646808680632007632105639334 * X + -2269883623590828149683334655101 * X^2 + -259550575000014576882296528413 * X^3 + 350509861317269046767503533227 * X^4 + 287435256848120756346068972613 * X^5 + 106803281774540017242044229607 * X^6 + 3711449772870929363858484967 * X^7 + -22025199213488411427482290194 * X^8 + -15177646119668505009197796321 * X^9 + -4834258721220318958198204898 * X^10 + 327565538376986978148250573 * X^11 + 1319194828319505042724893403 * X^12 + 783370486244227013785936801 * X^13 + 207811780706104230322313826 * X^14 + -44071987849765008968693660 * X^15 + -76227596573402910298004195 * X^16 + -39501681563242142038454504 * X^17 + -8256152010331500987058824 * X^18 + 3665540994387150681475715 * X^19 + 4273765076810885682585747 * X^20 + 1942221079153608429857654 * X^21 + 285677359204481998431203 * X^22 + -258702517814416564184449 * X^23 + -233671970486559087836791 * X^24 + -92787250839518213671860 * X^25 + -6900779040238441360106 * X^26 + 16730684113820513150396 * X^27 + 12465178344889516978598 * X^28 + 4284423247165179184386 * X^29 + -65427522186550695202 * X^30 + -1023743908542505153018 * X^31 + -650865113225649293822 * X^32 + -188970800212968086522 * X^33 + 25922165228951286958 * X^34 + 60045821306149910892 * X^35 + 33154796164188702226 * X^36 + 7845782823360677451 * X^37 + -2488803344965248688 * X^38 + -3418387726363442889 * X^39 + -1652383214505672884 * X^40 + -291824620263151925 * X^41 + 187604871318516199 * X^42 + 188578427804164623 * X^43 + 79948606103526045 * X^44 + 8923411418249172 * X^45 + -12544292697746304 * X^46 + -10217019079987586 * X^47 + -3760276071621046 * X^48 + -105433052002893 * X^49 + 787083897647323 * X^50 + 535553884178097 * X^51 + 169684248901278 * X^52 + -12041166379159 * X^53 + -47046055753382 * X^54 + -27863817732139 * X^55 + -7254152649201 * X^56 + 1654007891389 * X^57 + 2705731606530 * X^58 + 1383948934410 * X^59 + 289632561122 * X^60 + -129264657009 * X^61 + -152654645057 * X^62 + -69341784018 * X^63 + -9559941043 * X^64 + 9503541118 * X^65 + 8204430274 * X^66 + 3210848492 * X^67 + 256074184 * X^68 + -583936698 * X^69 + -449995342 * X^70 + -154230548 * X^71 + 5654684 * X^72 + 37410260 * X^73 + 22294959 * X^74 + 6406536 * X^75 + -739632 * X^76 + -2090343 * X^77 + -1235232 * X^78 + -284558 * X^79 + 108867 * X^80 + 123409 * X^81 + 53160 * X^82 + 9763 * X^83 + -5242 * X^84 + -6702 * X^85 + -3224 * X^86 + -292 * X^87 + 568 * X^88 + 349 * X^89 + 101 * X^90 + 6 * X^91 + -20 * X^92 + -21 * X^93 + -9 * X^94 + 2 * X^96 + -1 * X^99 + -1 * X^100 + -1 * X^101 + -1 * X^102

noncomputable def W_A : ℤ[X] := 135321183164940330816258139795353 + 138310817025696432198434746622664 * X + 74630956886239262370565717162838 * X^2 + 38321238048920005500635042786957 * X^3 + 8450674011606141763058223642628 * X^4

noncomputable def W_Q2 : ℤ[X] := 11181225461 + 3053503666 * X + -583892858 * X^2 + -1075869569 * X^3 + -557787146 * X^4 + -108167138 * X^5 + 66466555 * X^6 + 78507630 * X^7 + 44803978 * X^8 + 17306596 * X^9 + 4487669 * X^10 + 636183 * X^11

noncomputable def W_T : ℤ[X] := -290711440068 + -79386042606 * X + -18335369989 * X^2 + -14643936526 * X^3 + 18471559929 * X^4


theorem h109 : (109 : (ZMod 109)[X]) = 0 := by
  have h0 : (109 : ZMod 109) = 0 := by decide
  rw [← Polynomial.C_ofNat, h0, map_zero]


theorem red_X : red X = X := by
  simp only [red, Polynomial.coe_mapRingHom, Polynomial.map_X]


theorem bezout_lin_Z : u1Z * Rint109 + v1Z * (X ^ 109 - X) = 1 + 109 * W_lin := by
  unfold u1Z Rint109 v1Z W_lin
  ring


theorem bezout_quad_small_Z : aqZ * Rint109 + bqZ * S109Z = 1 + 109 * W_quad := by
  unfold aqZ Rint109 bqZ S109Z W_quad
  ring


theorem hA_Z : X ^ 109 = Q_Z * Rint109 + A_Z := by
  unfold Q_Z Rint109 A_Z
  ring


theorem hQZ_sub : Q_Z - Q_Z' = 109 * W_Q := by
  unfold Q_Z Q_Z' W_Q
  ring


theorem hAZ_sub : A_Z - Apr = 109 * W_A := by
  unfold A_Z Apr W_A
  ring


theorem hQ2Z_sub : Q2_Z - Q2_Z' = 109 * W_Q2 := by
  unfold Q2_Z Q2_Z' W_Q2
  ring


theorem hTZ_sub : T_Z - T_Z' = 109 * W_T := by
  unfold T_Z T_Z' W_T
  ring


theorem map_u1Z : red u1Z = u1 := by simp [red, u1Z, u1, Polynomial.C_ofNat]

theorem map_v1Z : red v1Z = v1 := by simp [red, v1Z, v1, Polynomial.C_ofNat]

theorem map_aqZ : red aqZ = aq := by simp [red, aqZ, aq, Polynomial.C_ofNat]

theorem map_bqZ : red bqZ = bq := by simp [red, bqZ, bq, Polynomial.C_ofNat]

theorem map_S109Z : red S109Z = S109 := by simp [red, S109Z, S109, Polynomial.C_ofNat]

theorem map_Rint : red Rint109 = R109 := by simp [red, Rint109, R109]

theorem map_Apr : red Apr = A := by simp [red, Apr, A, Polynomial.C_ofNat]


theorem map_Q_Z : red Q_Z = Q := by
  have h1 : red Q_Z' = Q := by simp [red, Q_Z', Q, Polynomial.C_ofNat]
  have h2 : red (Q_Z - Q_Z') = 0 := by
    rw [hQZ_sub]
    simp only [map_mul, map_ofNat, h109, zero_mul]
  have h3 : red Q_Z = red Q_Z' := by
    have h4 : red Q_Z - red Q_Z' = 0 := by
      rw [← map_sub]
      exact h2
    exact sub_eq_zero.mp h4
  rw [h3, h1]


theorem map_A_Z : red A_Z = A := by
  have h2 : red (A_Z - Apr) = 0 := by
    rw [hAZ_sub]
    simp only [map_mul, map_ofNat, h109, zero_mul]
  have h3 : red A_Z = red Apr := by
    have h4 : red A_Z - red Apr = 0 := by
      rw [← map_sub]
      exact h2
    exact sub_eq_zero.mp h4
  rw [h3, map_Apr]


theorem map_Q2_Z : red Q2_Z = Q2 := by
  have h1 : red Q2_Z' = Q2 := by simp [red, Q2_Z', Q2, Polynomial.C_ofNat]
  have h2 : red (Q2_Z - Q2_Z') = 0 := by
    rw [hQ2Z_sub]
    simp only [map_mul, map_ofNat, h109, zero_mul]
  have h3 : red Q2_Z = red Q2_Z' := by
    have h4 : red Q2_Z - red Q2_Z' = 0 := by
      rw [← map_sub]
      exact h2
    exact sub_eq_zero.mp h4
  rw [h3, h1]


theorem map_T_Z : red T_Z = T109 := by
  have h1 : red T_Z' = T109 := by simp [red, T_Z', T109, Polynomial.C_ofNat]
  have h2 : red (T_Z - T_Z') = 0 := by
    rw [hTZ_sub]
    simp only [map_mul, map_ofNat, h109, zero_mul]
  have h3 : red T_Z = red T_Z' := by
    have h4 : red T_Z - red T_Z' = 0 := by
      rw [← map_sub]
      exact h2
    exact sub_eq_zero.mp h4
  rw [h3, h1]


theorem map_S_Z' : red S_Z' = S109 := by simp [red, S_Z', S109, Polynomial.C_ofNat]

theorem map_T_Z' : red T_Z' = T109 := by simp [red, T_Z', T109, Polynomial.C_ofNat]



/-! ### F109 Bezout theorems -/

theorem bezout_lin : u1 * R109 + v1 * (X ^ 109 - X) = 1 := by
  have h := congrArg red bezout_lin_Z
  simp only [map_add, map_sub, map_mul, map_pow, red_X, map_one,
    map_u1Z, map_v1Z, map_Rint, map_ofNat, h109, zero_mul, add_zero] at h
  exact h


theorem bezout_quad_small : aq * R109 + bq * S109 = 1 := by
  have h := congrArg red bezout_quad_small_Z
  simp only [map_add, map_mul, map_one, map_aqZ, map_bqZ, map_S109Z, map_Rint,
    map_ofNat, h109, zero_mul, add_zero] at h
  exact h


/-! ### Frobenius chain -/

theorem hA : X ^ 109 = Q * R109 + A := by
  have h := congrArg red hA_Z
  simp only [map_add, map_mul, map_pow, red_X, map_Q_Z, map_A_Z, map_Rint] at h
  exact h


theorem hS_Z : 33 + 100 * Apr + 87 * Apr ^ 2 + 56 * Apr ^ 3 + 37 * Apr ^ 4
    = Q2_Z * Rint109 + T_Z := by
  unfold Apr Q2_Z Rint109 T_Z
  ring


theorem hS : (33 : (ZMod 109)[X]) + 100 * A + 87 * A ^ 2 + 56 * A ^ 3 + 37 * A ^ 4
    = Q2 * R109 + T109 := by
  have h := congrArg red hS_Z
  simp only [map_add, map_mul, map_pow, map_ofNat, map_Apr, map_Q2_Z, map_T_Z,
    map_Rint] at h
  exact h


theorem hA109 : A ^ 109 = (33 : (ZMod 109)[X]) + 100 * X ^ 109 + 87 * X ^ (2 * 109)
    + 56 * X ^ (3 * 109) + 37 * X ^ (4 * 109) := by
  have h33 : (33 : ZMod 109) ^ 109 = 33 := by decide
  have h100 : (100 : ZMod 109) ^ 109 = 100 := by decide
  have h87 : (87 : ZMod 109) ^ 109 = 87 := by decide
  have h56 : (56 : ZMod 109) ^ 109 = 56 := by decide
  have h37 : (37 : ZMod 109) ^ 109 = 37 := by decide
  show (C 33 + C 100 * X + C 87 * X ^ 2 + C 56 * X ^ 3 + C 37 * X ^ 4 : (ZMod 109)[X]) ^ 109
      = (33 : (ZMod 109)[X]) + 100 * X ^ 109 + 87 * X ^ (2 * 109)
        + 56 * X ^ (3 * 109) + 37 * X ^ (4 * 109)
  rw [add_pow_char, add_pow_char, add_pow_char, add_pow_char]
  rw [mul_pow, mul_pow, mul_pow, mul_pow]
  rw [← Polynomial.C_pow, ← Polynomial.C_pow, ← Polynomial.C_pow, ← Polynomial.C_pow,
    ← Polynomial.C_pow]
  rw [h33, h100, h87, h56, h37]
  rw [Polynomial.C_ofNat, Polynomial.C_ofNat, Polynomial.C_ofNat, Polynomial.C_ofNat,
    Polynomial.C_ofNat]
  rw [pow_mul, pow_mul, pow_mul]


theorem hsub : X ^ 109 - A = Q * R109 := by linear_combination hA


theorem key : ∀ i : ℕ, ∃ D, X ^ (i * 109) - A ^ i = R109 * D := by
  intro i
  obtain ⟨E, hE⟩ := sub_dvd_pow_sub_pow (X ^ 109) A i
  refine ⟨Q * E, ?_⟩
  have h1 : ((X : (ZMod 109)[X]) ^ 109) ^ i = (X : (ZMod 109)[X]) ^ (i * 109) := by rw [← pow_mul, mul_comm]
  rw [← h1, hE, hsub]
  ring


theorem hTS_Z : T_Z' = S_Z' + X := by
  unfold T_Z' S_Z'
  ring


theorem hTS : T109 = S109 + X := by
  have h := congrArg red hTS_Z
  simp only [map_add, red_X, map_T_Z', map_S_Z'] at h
  exact h


theorem quad_mod : ((X : (ZMod 109)[X]) ^ (109 ^ 2) - (X : (ZMod 109)[X])) % R109 = S109 := by
  obtain ⟨D0, hD0⟩ := key 0
  obtain ⟨D1, hD1⟩ := key 1
  obtain ⟨D2, hD2⟩ := key 2
  obtain ⟨D3, hD3⟩ := key 3
  obtain ⟨D4, hD4⟩ := key 4
  have hpow : (X : (ZMod 109)[X]) ^ (109 ^ 2) = ((X : (ZMod 109)[X]) ^ 109) ^ 109 := by
    rw [← pow_mul, pow_two]
  have hX : X ^ (109 ^ 2)
      = (Q ^ 109 * R109 ^ 108 + Q2 + (33 * D0 + 100 * D1 + 87 * D2 + 56 * D3
        + 37 * D4)) * R109 + T109 := by
    rw [hpow, hA, add_pow_char, mul_pow, hA109]
    have hsum : (33 : (ZMod 109)[X]) + 100 * X ^ 109 + 87 * X ^ (2 * 109)
        + 56 * X ^ (3 * 109) + 37 * X ^ (4 * 109)
        = ((33 : (ZMod 109)[X]) + 100 * A + 87 * A ^ 2 + 56 * A ^ 3 + 37 * A ^ 4)
          + (33 * D0 + 100 * D1 + 87 * D2 + 56 * D3 + 37 * D4) * R109 := by
      linear_combination 33 * hD0 + 100 * hD1 + 87 * hD2 + 56 * hD3 + 37 * hD4
    rw [hsum, hS]
    ring
  have hdiv : R109 ∣ (X ^ (109 ^ 2) - X) - S109 := by
    refine ⟨Q ^ 109 * R109 ^ 108 + Q2 + (33 * D0 + 100 * D1 + 87 * D2 + 56 * D3
      + 37 * D4), ?_⟩
    linear_combination hX + hTS
  have hSnd : S109.natDegree = 4 := by simp only [S109]; compute_degree!
  have hSne : S109 ≠ 0 := Polynomial.ne_zero_of_natDegree_gt (n := 0) (by rw [hSnd]; norm_num)
  have hRnd : R109.natDegree = 5 := by simp only [R109]; compute_degree!
  have hRne : R109 ≠ 0 := Polynomial.ne_zero_of_natDegree_gt (n := 0) (by rw [hRnd]; norm_num)
  have hdeg : S109.degree < R109.degree := by
    rw [Polynomial.degree_eq_natDegree hSne, Polynomial.degree_eq_natDegree hRne, hSnd, hRnd]
    decide
  rw [Polynomial.mod_eq_of_dvd_sub hdiv, Polynomial.mod_eq_self_iff hRne]
  exact hdeg

end BranchC.GradeA
