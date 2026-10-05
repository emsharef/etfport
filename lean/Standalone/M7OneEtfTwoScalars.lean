import Mathlib.Analysis.Calculus.Deriv.Basic
import Mathlib.Topology.Order.Basic
import Mathlib.Algebra.Order.BigOperators.Group.Finset

/-!
# Claim 110: one ETF and any number of funds, decided by two scalars

Statement only; the proof is `Novel/M7OneEtfTwoScalarsProof.lean`.

The model is the claim's own one-ETF coordinates, claim 040's coordinates with one ETF, fees in, and
the ETF's rates and incumbent added (`One`). The fund data are the net alpha plus fee credit `α~_i`,
the netting weight `r_i`, the residual variance `v_i`, the rates, the cap and the incumbent. The ETF
data are the exposure premium net of fee `μ_E`, `σ_EE`, the ETF's own residual variance `σ_E`, its
rates and its incumbent `p⁻ ≥ 0`; the ETF has no cap. The model also has `γ` and the cash `h⁻`.
- `Q(x, p)` is the review's objective with `w = p + Σ_i r_i x_i`.
- `k(x, p) = h⁻ - Σ_i (x_i - x⁻_i) - (p - p⁻) - C_A(x - x⁻) - C_E(p - p⁻)` is the funded budget.
- `lag η = Q + η k` is the Lagrangian.
- `m(w) = μ_E - γσ_EE w` is the exposure price, and `xi m η` and `pf m η` are the claim's one-fund
  clips and ETF holding at prices `(m, η)`.
- `eF m η = m - γσ_E pf m η` is the ETF's own marginal at the price `m` (part 5; it is `m` when
  `σ_E = 0`).

Scope (PM, rule 6b). Formal: parts 1, 2, 3 (without the existence of `η`), 4(a)-(b) and 5. Part 3
is conditional. It shows that `x(0)` is the constrained optimum when `k(x(0)) ≥ 0`, and that any `η > 0`
with `k(x(η)) = 0` gives it. The existence of such an `η` when `k(x(0)) < 0` is the standard KKT
multiplier, cited through AX-13 (claim 102's part 1, rule 21) and paper-level. These coordinates are
not linked formally to claim 027's `Data` with a budget. Part 4(c) and the Checks are paper-level.
-/

namespace Standalone.M7OneEtfTwoScalars

noncomputable section

/-- The claim's one-ETF instance with `N` funds. -/
structure One (N : ℕ) where
  alt : Fin N → ℝ
  r : Fin N → ℝ
  v : Fin N → ℝ
  kp : Fin N → ℝ
  km : Fin N → ℝ
  xbar : Fin N → ℝ
  xm : Fin N → ℝ
  muE : ℝ
  sEE : ℝ
  sE : ℝ
  kpE : ℝ
  kmE : ℝ
  pm : ℝ
  gamma : ℝ
  h : ℝ

variable {N : ℕ}

/-- The standing assumptions: `γ, σ_EE, v_i, h⁻ > 0`, `σ_E ≥ 0`, nonnegative rates with sale rates
below one, `0 ≤ x⁻ ≤ x̄` and `p⁻ ≥ 0`. -/
def Hyp (P : One N) : Prop :=
  0 < P.gamma ∧ 0 < P.sEE ∧ 0 ≤ P.sE ∧ 0 < P.h ∧ 0 ≤ P.kpE ∧ 0 ≤ P.kmE ∧ P.kmE < 1 ∧ 0 ≤ P.pm ∧
    ∀ i, 0 < P.v i ∧ 0 ≤ P.kp i ∧ 0 ≤ P.km i ∧ P.km i < 1 ∧ 0 ≤ P.xm i ∧ P.xm i ≤ P.xbar i

/-- A proportional cost `κ⁺u⁺ + κ⁻u⁻`. -/
def pc (kp km u : ℝ) : ℝ := kp * max u 0 + km * max (-u) 0

/-- The total exposure `w = p + Σ_i r_i x_i`. -/
def wx (P : One N) (x : Fin N → ℝ) (p : ℝ) : ℝ := p + ∑ i, P.r i * x i

/-- The funds' trade cost `C_A(x - x⁻)`. -/
def costA (P : One N) (x : Fin N → ℝ) : ℝ := ∑ i, pc (P.kp i) (P.km i) (x i - P.xm i)

/-- The review's objective. -/
def Qobj (P : One N) (x : Fin N → ℝ) (p : ℝ) : ℝ :=
  ∑ i, (P.alt i * x i - P.gamma * P.v i / 2 * x i ^ 2) + P.muE * wx P x p -
    P.gamma * P.sEE / 2 * wx P x p ^ 2 - P.gamma * P.sE / 2 * p ^ 2 - costA P x -
      pc P.kpE P.kmE (p - P.pm)

/-- The funded budget `k(x, p)`. -/
def kb (P : One N) (x : Fin N → ℝ) (p : ℝ) : ℝ :=
  P.h - ∑ i, (x i - P.xm i) - (p - P.pm) - costA P x - pc P.kpE P.kmE (p - P.pm)

/-- The feasible set without the budget: funds in their box, the ETF long. -/
def S (P : One N) : Set ((Fin N → ℝ) × ℝ) := {z | (∀ i, 0 ≤ z.1 i ∧ z.1 i ≤ P.xbar i) ∧ 0 ≤ z.2}

/-- The Lagrangian `Q + η k`. -/
def lag (P : One N) (η : ℝ) (z : (Fin N → ℝ) × ℝ) : ℝ := Qobj P z.1 z.2 + η * kb P z.1 z.2

/-- The exposure price `m(w) = μ_E - γ σ_EE w`. -/
def mw (P : One N) (w : ℝ) : ℝ := P.muE - P.gamma * P.sEE * w

/-- The ETF's scaled purchase threshold `θ_b(η) = η + (1 + η) κ⁺_E`. -/
def thb (P : One N) (η : ℝ) : ℝ := η + (1 + η) * P.kpE

/-- The ETF's scaled sale threshold `θ_s(η) = η - (1 + η) κ⁻_E`. -/
def ths (P : One N) (η : ℝ) : ℝ := η - (1 + η) * P.kmE

/-- Fund `i`'s one-fund clip at prices `(m, η)`: `clip(x⁻_i, lo_i, hi_i)` clipped to `[0, x̄_i]`. -/
def xi (P : One N) (m η : ℝ) (i : Fin N) : ℝ :=
  max 0 (min (P.xbar i) (max ((P.alt i + P.r i * m - η - (1 + η) * P.kp i) / (P.gamma * P.v i))
    (min ((P.alt i + P.r i * m - η + (1 + η) * P.km i) / (P.gamma * P.v i)) (P.xm i))))

/-- The funds' by-product `q(m, η) = Σ_i r_i x_i(m, η)`. -/
def qf (P : One N) (m η : ℝ) : ℝ := ∑ i, P.r i * xi P m η i

/-- The ETF holding at prices `(m, η)`: `p(m, η) = w(m) - q(m, η)`. -/
def pf (P : One N) (m η : ℝ) : ℝ := (P.muE - m) / (P.gamma * P.sEE) - qf P m η

/-- The ETF's own marginal at the price `m`: `m - γ σ_E p(m, η)`. -/
def eF (P : One N) (m η : ℝ) : ℝ := m - P.gamma * P.sE * pf P m η

/-- The root of a function, when it exists. -/
def root (f : ℝ → ℝ) (c : ℝ) : ℝ := Classical.epsilon fun m => f m = c

/-- The at-zero candidate `m_0(η)`: the root of `p(m, η) = 0`. -/
def m0 (P : One N) (η : ℝ) : ℝ := root (fun m => pf P m η) 0

/-- The idle candidate `m_I(η)`: the root of `p(m, η) = p⁻`. -/
def mI (P : One N) (η : ℝ) : ℝ := root (fun m => pf P m η) P.pm

/-- The traded price at a threshold `θ`: the root of `m - γσ_E p(m, η) = θ` (`θ` itself when `σ_E = 0`). -/
def mT (P : One N) (η θ : ℝ) : ℝ := root (fun m => eF P m η) θ

/-- One fund's problem at prices `(m, η)`. -/
def phi (P : One N) (m η : ℝ) (i : Fin N) (x : ℝ) : ℝ :=
  (P.alt i + P.r i * m - η) * x - P.gamma * P.v i / 2 * x ^ 2 - (1 + η) * pc (P.kp i) (P.km i) (x - P.xm i)

/-! ### Part 1 -/

/-- Part 1: the clip is the unique maximizer of the one-fund problem at prices `(m, η)`. `r_i x_i` is
nondecreasing in `m`, and `x_i` is nonincreasing in `η ≥ 0`. `q(·, η)` is continuous, nondecreasing
and bounded by `Σ_i |r_i| x̄_i`. `p(·, η)` is continuous and strictly decreasing, and takes every value
exactly once, so `m_0` and `m_I` exist and are unique. So does `m - γσ_E p(m, η)`, which is strictly
increasing, so the traded prices exist and are unique. -/
def OnePrice : Prop :=
  ∀ (N : ℕ) (P : One N), Hyp P →
    (∀ m η i, 0 ≤ η →
      (0 ≤ xi P m η i ∧ xi P m η i ≤ P.xbar i) ∧
      (∀ y, 0 ≤ y → y ≤ P.xbar i → phi P m η i y ≤ phi P m η i (xi P m η i)) ∧
      ∀ y, 0 ≤ y → y ≤ P.xbar i → (∀ y', 0 ≤ y' → y' ≤ P.xbar i → phi P m η i y' ≤ phi P m η i y) →
        y = xi P m η i) ∧
    (∀ η i, Monotone fun m => P.r i * xi P m η i) ∧
    (∀ m i, AntitoneOn (fun η => xi P m η i) (Set.Ici 0)) ∧
    (∀ η, Continuous (fun m => qf P m η) ∧ Monotone (fun m => qf P m η) ∧
      ∀ m, |qf P m η| ≤ ∑ i, |P.r i| * P.xbar i) ∧
    (∀ η, Continuous (fun m => pf P m η) ∧ StrictAnti (fun m => pf P m η) ∧
      ∀ c, ∃! m, pf P m η = c) ∧
    (∀ η, StrictMono (fun m => eF P m η) ∧ ∀ c, ∃! m, eF P m η = c)

/-- Part 1's identity: fund `i`'s smooth marginal is `α~_i + r_i m(w) - γ v_i x_i`, whatever `σ_E`
(the derivative of the smooth objective along coordinate `i`). -/
def Marginal : Prop :=
  ∀ (N : ℕ) (P : One N) (x : Fin N → ℝ) (p : ℝ) (i : Fin N),
    HasDerivAt (fun t => ∑ j, (P.alt j * Function.update x i t j - P.gamma * P.v j / 2 * Function.update x i t j ^ 2) +
        P.muE * wx P (Function.update x i t) p - P.gamma * P.sEE / 2 * wx P (Function.update x i t) p ^ 2 -
        P.gamma * P.sE / 2 * p ^ 2)
      (P.alt i + P.r i * mw P (wx P x p) - P.gamma * P.v i * x i) (x i)

/-! ### Parts 2 and 5: the ETF's status given the cash price -/

/-- Parts 2 and 5, for each `η ≥ 0`. The Lagrangian `Q + η k` has exactly one maximizer over the funds'
boxes and `p ≥ 0`. At it, with `m = m(w)`, every fund holds its clip `x_i(m, η)`, `p = p(m, η)`, and
the ETF's status is read off the table. `e(m) = m - γσ_E p(m, η)` is the ETF's own marginal, and
`m_b`, `m_s` are the traded prices at `θ_b`, `θ_s`.
- For `p⁻ > 0`: bought iff `e(m_I) > θ_b` (then `m = m_b`, `p > p⁻`); idle iff
  `θ_s ≤ e(m_I) ≤ θ_b` (then `m = m_I`, `p = p⁻`); sold iff `e(m_I) < θ_s`, either to
  `p(m_s) ∈ (0, p⁻)` with `m = m_s` if `m_0 > θ_s`, or to zero with `m = m_0` if `m_0 ≤ θ_s`.
- For `p⁻ = 0`: at zero iff `m_0 ≤ θ_b` (then `m = m_0`), bought iff `m_0 > θ_b` (then `m = m_b`,
  `p > 0`).
With `σ_E = 0`, `e(m) = m`, `m_b = θ_b` and `m_s = θ_s` (part 2's table). -/
def Status : Prop :=
  ∀ (N : ℕ) (P : One N), Hyp P → ∀ η, 0 ≤ η →
    (∃! z, z ∈ S P ∧ IsMaxOn (lag P η) (S P) z) ∧
    ∀ z ∈ S P, IsMaxOn (lag P η) (S P) z →
      let m := mw P (wx P z.1 z.2)
      let e := fun m' => eF P m' η
      let mb := mT P η (thb P η)
      let ms := mT P η (ths P η)
      (∀ i, z.1 i = xi P m η i) ∧ z.2 = pf P m η ∧
      (0 < P.pm →
        ((P.pm < z.2 ↔ thb P η < e (mI P η)) ∧ (thb P η < e (mI P η) → m = mb)) ∧
        ((z.2 = P.pm ↔ ths P η ≤ e (mI P η) ∧ e (mI P η) ≤ thb P η) ∧
          (ths P η ≤ e (mI P η) → e (mI P η) ≤ thb P η → m = mI P η)) ∧
        ((z.2 < P.pm ↔ e (mI P η) < ths P η) ∧
          (e (mI P η) < ths P η → ths P η < m0 P η → m = ms ∧ 0 < z.2) ∧
          (e (mI P η) < ths P η → m0 P η ≤ ths P η → m = m0 P η ∧ z.2 = 0))) ∧
      (P.pm = 0 →
        (z.2 = 0 ↔ m0 P η ≤ thb P η) ∧ (m0 P η ≤ thb P η → m = m0 P η) ∧
        (thb P η < m0 P η → m = mb ∧ 0 < z.2)) ∧
      (P.sE = 0 → mb = thb P η ∧ ms = ths P η ∧ ∀ m', e m' = m')

/-! ### Part 3: the cash price -/

/-- The Lagrangian maximizer at `η` (unique by `Status`). -/
def zOpt (P : One N) (η : ℝ) : (Fin N → ℝ) × ℝ :=
  Classical.epsilon fun z => z ∈ S P ∧ IsMaxOn (lag P η) (S P) z

/-- Part 3: the cash slack `k(x(η))` is nondecreasing in `η ≥ 0`. If `k(x(0)) ≥ 0`, `x(0)` is the
constrained optimum. Every `η > 0` with `k(x(η)) = 0` gives the constrained optimum, so all such `η`
give the same holdings. -/
def CashPrice : Prop :=
  ∀ (N : ℕ) (P : One N), Hyp P →
    MonotoneOn (fun η => kb P (zOpt P η).1 (zOpt P η).2) (Set.Ici 0) ∧
    (0 ≤ kb P (zOpt P 0).1 (zOpt P 0).2 →
      zOpt P 0 ∈ S P ∧ IsMaxOn (fun z => Qobj P z.1 z.2) {z | z ∈ S P ∧ 0 ≤ kb P z.1 z.2} (zOpt P 0)) ∧
    ∀ η, 0 < η → kb P (zOpt P η).1 (zOpt P η).2 = 0 →
      zOpt P η ∈ S P ∧
        IsMaxOn (fun z => Qobj P z.1 z.2) {z | z ∈ S P ∧ 0 ≤ kb P z.1 z.2} (zOpt P η) ∧
        ∀ z, z ∈ S P → 0 ≤ kb P z.1 z.2 →
          IsMaxOn (fun z => Qobj P z.1 z.2) {z | z ∈ S P ∧ 0 ≤ kb P z.1 z.2} z → z = zOpt P η

/-! ### Part 4: readings -/

/-- Part 4(a): at prices `(m, η)`, fund `i` is bought iff `α~_i + r_i m - γ v_i x⁻_i > η + (1 + η)κ⁺_i` and
`x⁻_i < x̄_i`, and sold iff `α~_i + r_i m - γ v_i x⁻_i < η - (1 + η)κ⁻_i` and `x⁻_i > 0`. Part 4(b): on
every piece, a price change moves fund `i` by at most `|r_i|/(γ v_i)` per unit. -/
def Readings : Prop :=
  ∀ (N : ℕ) (P : One N), Hyp P → ∀ m η i, 0 ≤ η →
    (P.xm i < xi P m η i ↔
      η + (1 + η) * P.kp i < P.alt i + P.r i * m - P.gamma * P.v i * P.xm i ∧ P.xm i < P.xbar i) ∧
    (xi P m η i < P.xm i ↔
      P.alt i + P.r i * m - P.gamma * P.v i * P.xm i < η - (1 + η) * P.km i ∧ 0 < P.xm i) ∧
    ∀ m', |xi P m' η i - xi P m η i| ≤ |P.r i| / (P.gamma * P.v i) * |m' - m|

/-- Claim 110 (parts 1-5; part 3's existence of `η*` and part 4(c) are paper-level). -/
def statement : Prop := OnePrice ∧ Marginal ∧ Status ∧ CashPrice ∧ Readings

end

end Standalone.M7OneEtfTwoScalars
