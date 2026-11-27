import FormalConjectures.OptimizationConstants.«6a»
import Mathlib

-- Ronak Patel / Avon Labs (@ronak14p).
-- We follow the entropy argument of Chase and Lovett (arXiv:2211.11689).
-- The scalar inequality uses the port attributed below. The remaining sections
-- pass to two variables, compare each conditional entropy increment under union,
-- and sum the increments for a uniform random member of the finite family.

section
/-
Scalar proof adapted from https://github.com/boonsuan/entropy-inequality by Ho Boon Suan and Aristotle (Harmonic).
MIT License

Copyright (c) 2026 ho boon suan

Permission is hereby granted, free of charge, to any person obtaining a copy
of this software and associated documentation files (the "Software"), to deal
in the Software without restriction, including without limitation the rights
to use, copy, modify, merge, publish, distribute, sublicense, and/or sell
copies of the Software, and to permit persons to whom the Software is
furnished to do so, subject to the following conditions:

The above copyright notice and this permission notice shall be included in all
copies or substantial portions of the Software.

THE SOFTWARE IS PROVIDED "AS IS", WITHOUT WARRANTY OF ANY KIND, EXPRESS OR
IMPLIED, INCLUDING BUT NOT LIMITED TO THE WARRANTIES OF MERCHANTABILITY,
FITNESS FOR A PARTICULAR PURPOSE AND NONINFRINGEMENT. IN NO EVENT SHALL THE
AUTHORS OR COPYRIGHT HOLDERS BE LIABLE FOR ANY CLAIM, DAMAGES OR OTHER
LIABILITY, WHETHER IN AN ACTION OF CONTRACT, TORT OR OTHERWISE, ARISING FROM,
OUT OF OR IN CONNECTION WITH THE SOFTWARE OR THE USE OR OTHER DEALINGS IN THE
SOFTWARE.
-/

namespace C6Scalar
open scoped BigOperators Real Nat Classical Pointwise

/-
For $k > 1$, $\alpha_k$ is the unique positive solution to $x(1+x)^{k-1}=1$.
-/
set_option maxHeartbeats 1000000 in
set_option maxRecDepth 4000 in
lemma alpha_exists (k : ℝ) (hk : k > 1) :
    ∃ x : ℝ, x > 0 ∧ x * (1 + x) ^ (k - 1) = 1 := by
  -- By the Intermediate Value Theorem, since $f(0) = 0$ and $f(1) = 2^{k - 1} > 1$.
  have h_image :
      (1 : ℝ) ∈ (fun x : ℝ => x * (1 + x) ^ (k - 1)) '' Set.Ioo (0 : ℝ) 1 := by
    refine
      (intermediate_value_Ioo (a := (0 : ℝ)) (b := (1 : ℝ))
          (f := fun x : ℝ => x * (1 + x) ^ (k - 1)) (by norm_num) ?_) ?_
    ·
      exact
        continuousOn_of_forall_continuousAt fun x hx =>
          ContinuousAt.mul continuousAt_id <|
            ContinuousAt.rpow (continuousAt_const.add continuousAt_id) continuousAt_const <|
              Or.inl <| by linarith [hx.1]
    · constructor
      · norm_num
      ·
        have hpow : (1 : ℝ) < (1 + 1) ^ (k - 1) := by
          exact Real.one_lt_rpow (by norm_num : (1 : ℝ) < (1 + 1)) (by linarith [hk])
        simpa using hpow
  rcases h_image with ⟨x, hx, hx_eq⟩
  exact ⟨x, hx.1, hx_eq⟩

noncomputable def alpha (k : ℝ) : ℝ :=
  if hk : k > 1 then
    Classical.choose (alpha_exists k hk)
  else 0

set_option maxHeartbeats 1000000 in
set_option maxRecDepth 4000 in
lemma alpha_spec (k : ℝ) (hk : k > 1) :
    alpha k > 0 ∧ alpha k * (1 + alpha k) ^ (k - 1) = 1 := by
  unfold alpha
  simpa [hk] using (Classical.choose_spec (alpha_exists k hk))

set_option maxHeartbeats 1000000 in
set_option maxRecDepth 4000 in
lemma alpha_pos (k : ℝ) (hk : k > 1) : 0 < alpha k :=
  (alpha_spec k hk).1

/-
For $k > 1$, $\alpha_k > 1/k$.
-/
set_option maxHeartbeats 1000000 in
set_option maxRecDepth 4000 in
lemma lemma_l2 (k : ℝ) (hk : k > 1) : alpha k > 1 / k := by
  -- Set $f(x) = x(1+x)^{k-1}$.
  set f := fun x : ℝ => x * (1 + x) ^ (k - 1);
  -- Since $f$ is strictly increasing on $(0, \infty)$, it suffices to check that $f(1/k) < 1$.
  have h_f1k_lt_1 : f (1 / k) < 1 := by
    -- Simplify $f(1/k)$ to get $(1/k) * (1 + 1/k)^{k-1} < 1$.
    have h_simplified : (1 / k) * (1 + 1 / k) ^ (k - 1) < 1 := by
      -- Simplify the expression $(1 / k) * (1 + 1 / k) ^ (k - 1)$ to $(1 + 1 / k) ^ (k - 1) / k$.
      suffices h_simplified' : (1 + 1 / k) ^ (k - 1) < k by
        rw [ div_mul_eq_mul_div, div_lt_iff₀ ] <;> linarith;
      -- Taking the natural logarithm of both sides, we need to show that $(k-1) \ln(1 + 1/k) < \ln(k)$.
      suffices h_ln : (k - 1) * Real.log (1 + 1 / k) < Real.log k by
        rw [ ← Real.log_lt_log_iff ( by positivity ) ( by positivity ), Real.log_rpow ( by positivity ) ] ; linarith;
      -- We'll use the fact that $Real.log (1 + x) < x$ for all $x > 0$.
      have h_log_lt : Real.log (1 + 1 / k) < 1 / k := by
        simpa using Real.log_lt_sub_one_of_pos ( add_pos zero_lt_one ( one_div_pos.mpr ( zero_lt_one.trans hk ) ) ) ( by nlinarith [ one_div_mul_cancel ( by linarith : k ≠ 0 ) ] );
      rw [ lt_div_iff₀ ] at h_log_lt <;> nlinarith [ Real.log_inv k ▸ Real.log_lt_sub_one_of_pos ( inv_pos.mpr <| zero_lt_one.trans hk ) ( by nlinarith [ inv_mul_cancel₀ ( ne_of_gt <| zero_lt_one.trans hk ) ] ), mul_inv_cancel₀ ( ne_of_gt <| zero_lt_one.trans hk ) ];
    exact h_simplified;
  -- Since $f$ is strictly increasing on $(0, \infty)$, we have $f(\alpha_k) = 1$.
  have h_f_alpha_k : f (alpha k) = 1 := by
    simpa [f] using (alpha_spec k hk).2
  -- Since $f$ is strictly increasing on $(0, \infty)$, we have $f(\alpha_k) > f(1/k)$.
  have h_f_alpha_k_gt_f1k : f (alpha k) > f (1 / k) := by
    linarith;
  have hα_nonneg : 0 ≤ alpha k := (alpha_pos k hk).le
  have hk0 : k ≠ 0 := by linarith
  contrapose! h_f_alpha_k_gt_f1k;
  exact
    mul_le_mul
      (by nlinarith [mul_div_cancel₀ 1 hk0])
      (Real.rpow_le_rpow
        (by nlinarith [mul_div_cancel₀ 1 hk0, hα_nonneg])
        (by nlinarith [mul_div_cancel₀ 1 hk0, hα_nonneg])
        (by linarith))
      (by exact Real.rpow_nonneg (by nlinarith [mul_div_cancel₀ 1 hk0, hα_nonneg]) _)
      (by nlinarith [mul_div_cancel₀ 1 hk0, hα_nonneg])

/-
We have $\lim_{x\to 0^+}q(x)=1/k$.
-/
noncomputable def q (k : ℝ) (x : ℝ) : ℝ := x ^ (k - 1) * Real.binEntropy x / Real.binEntropy (x ^ k)

set_option maxHeartbeats 1000000 in
set_option maxRecDepth 4000 in
lemma lemma_l1_zero (k : ℝ) (hk : k > 1) :
    Filter.Tendsto (q k) (nhdsWithin 0 (Set.Ioi 0)) (nhds (1 / k)) := by
  unfold q;
  -- We'll use the fact that $h(x) = -x \log x + O(x)$ as $x \to 0$.
  have h_hx : Filter.Tendsto (fun x : ℝ => Real.binEntropy x / (-x * Real.log x)) (nhdsWithin 0 (Set.Ioi 0)) (nhds 1) := by
    -- We'll use the fact that $h(x) = -x \log x + O(x^2)$ to simplify the expression.
    have h_binEntropy_approx : Filter.Tendsto (fun x => (Real.binEntropy x - (-x * Real.log x)) / (-x * Real.log x)) (nhdsWithin 0 (Set.Ioi 0)) (nhds 0) := by
      -- We'll use the fact that $h(x) = -x \log x + O(x^2)$ to simplify the expression. Notice that $Real.binEntropy x = -x \log x - (1 - x) \log (1 - x)$.
      have h_binEntropy_approx : Filter.Tendsto (fun x => (-(1 - x) * Real.log (1 - x)) / (-x * Real.log x)) (nhdsWithin 0 (Set.Ioi 0)) (nhds 0) := by
        -- We'll use the fact that $\log(1 - x) \sim -x$ as $x \to 0$ to simplify the expression.
        have h_log_approx : Filter.Tendsto (fun x => Real.log (1 - x) / x) (nhdsWithin 0 (Set.Ioi 0)) (nhds (-1)) := by
          simpa [ div_eq_inv_mul ] using HasDerivAt.tendsto_slope_zero_right ( HasDerivAt.log ( hasDerivAt_id 0 |> HasDerivAt.const_sub 1 ) ( by norm_num ) );
        -- We'll use the fact that $(1 - x) \to 1$ as $x \to 0$.
        have h_one_minus_x : Filter.Tendsto (fun x : ℝ => (1 - x)) (nhdsWithin 0 (Set.Ioi 0)) (nhds 1) := by
          exact tendsto_nhdsWithin_of_tendsto_nhds ( Continuous.tendsto' ( by continuity ) _ _ <| by norm_num );
        convert h_one_minus_x.mul ( h_log_approx.div_atBot ( Real.tendsto_log_nhdsNE_zero.mono_left <| nhdsWithin_mono _ <| by norm_num ) ) using 2 <;> ring!;
      simp_all +decide [ Real.binEntropy ];
      exact h_binEntropy_approx.congr fun x => by ring;
    have := h_binEntropy_approx.const_add 1;
    simpa using this.congr' ( by filter_upwards [ ( Ioo_mem_nhdsGT_of_mem ⟨ le_rfl, zero_lt_one ⟩ ) ] with x hx using by rw [ one_add_div ( mul_ne_zero ( neg_ne_zero.mpr hx.1.ne' ) <| ne_of_lt <| Real.log_neg hx.1 hx.2 ) ] ; ring );
  -- Applying the asymptotic estimate to $h(x^k)$, we get $h(x^k) = -kx^k \log x + O(x^k)$.
  have h_hxk : Filter.Tendsto (fun x : ℝ => Real.binEntropy (x ^ k) / (-k * x ^ k * Real.log x)) (nhdsWithin 0 (Set.Ioi 0)) (nhds 1) := by
    have h_hxk : Filter.Tendsto (fun x : ℝ => (Real.binEntropy (x ^ k)) / (-x ^ k * Real.log (x ^ k))) (nhdsWithin 0 (Set.Ioi 0)) (nhds 1) := by
      exact h_hx.comp ( Filter.Tendsto.inf ( ContinuousAt.tendsto ( show ContinuousAt ( fun x : ℝ => x ^ k ) 0 by exact ContinuousAt.rpow continuousAt_id continuousAt_const <| Or.inr <| by linarith ) |> fun h => h.trans <| by norm_num [ show k ≠ 0 by linarith ] ) <| Filter.tendsto_principal_principal.mpr <| by intro x hx; exact Real.rpow_pos_of_pos hx _ );
    refine h_hxk.congr' ( by filter_upwards [ self_mem_nhdsWithin ] with x hx using by rw [ Real.log_rpow hx ] ; ring );
  have := h_hx.div h_hxk;
  simp_all +decide [ division_def ];
  convert this.const_mul ( k⁻¹ ) |> Filter.Tendsto.congr' _ using 2;
  · ring;
  · filter_upwards [ self_mem_nhdsWithin ] with x hx ; by_cases hx' : Real.binEntropy x = 0 <;> by_cases hx'' : Real.binEntropy ( x ^ k ) = 0 <;> simp_all +decide [mul_assoc,
    mul_comm, mul_left_comm];
    by_cases h : Real.log x = 0 <;> simp_all +decide [ Real.rpow_sub_one, mul_comm ];
    · rcases h with ( rfl | rfl | rfl ) <;> norm_num at *;
    · grind

/-
We have $\lim_{x\to 1^-}q(x)=1/k$.
-/
set_option maxHeartbeats 1000000 in
set_option maxRecDepth 4000 in
lemma lemma_l1_one (k : ℝ) (hk : k > 1) :
    Filter.Tendsto (q k) (nhdsWithin 1 (Set.Iio 1)) (nhds (1 / k)) := by
  -- By definition of $q_k(x)$, we know that $q_k(x) = \frac{x^{k-1} h(x)}{h(x^k)}$ where $h(x) = -x \log x - (1-x) \log (1-x)$.
  unfold q;
  -- By definition of $h(x)$, we know that $h(x) = -x \log x - (1-x) \log (1-x)$.
  unfold Real.binEntropy;
  -- We'll use the substitution $u = 1 - x$, so as $x \to 1^-$, $u \to 0^+$.
  suffices h_subst : Filter.Tendsto (fun u => ((1 - u) ^ (k - 1) * ((1 - u) * Real.log (1 - u)⁻¹ + u * Real.log u⁻¹)) / ((1 - u) ^ k * Real.log ((1 - u) ^ k)⁻¹ + (1 - (1 - u) ^ k) * Real.log (1 - (1 - u) ^ k)⁻¹)) (nhdsWithin 0 (Set.Ioi 0)) (nhds (1 / k)) by
    rw [ Metric.tendsto_nhdsWithin_nhds ] at *;
    intro ε hε; rcases h_subst ε hε with ⟨ δ, hδ, H ⟩ ; exact ⟨ δ, hδ, fun { x } hx₁ hx₂ => by convert H ( show 0 < 1 - x from by linarith [ hx₁.out ] ) ( by simpa [ dist_comm ] using hx₂ ) using 1; ring_nf ⟩ ;
  -- We'll use the fact that as $u \to 0$, $(1 - u)^k \approx 1 - ku$ and $\log(1 - u) \approx -u$.
  have h_approx : Filter.Tendsto (fun u => (1 - u) ^ (k - 1) * ((1 - u) * Real.log (1 - u)⁻¹ + u * Real.log u⁻¹) / (u * Real.log u⁻¹)) (nhdsWithin 0 (Set.Ioi 0)) (nhds 1) ∧ Filter.Tendsto (fun u => ((1 - u) ^ k * Real.log ((1 - u) ^ k)⁻¹ + (1 - (1 - u) ^ k) * Real.log (1 - (1 - u) ^ k)⁻¹) / (u * Real.log u⁻¹)) (nhdsWithin 0 (Set.Ioi 0)) (nhds k) := by
    constructor;
    · -- We'll use the fact that as $u \to 0$, $(1 - u) \log(1 - u)^{-1} \approx u$ and $u \log u^{-1} \approx u$.
      have h_approx : Filter.Tendsto (fun u => ((1 - u) * Real.log (1 - u)⁻¹ + u * Real.log u⁻¹) / (u * Real.log u⁻¹)) (nhdsWithin 0 (Set.Ioi 0)) (nhds 1) := by
        -- We'll use the fact that as $u \to 0$, $(1 - u) \log(1 - u)^{-1} \approx u$ and $u \log u^{-1} \approx u$ to simplify the expression.
        have h_approx : Filter.Tendsto (fun u => (1 - u) * Real.log (1 - u)⁻¹ / (u * Real.log u⁻¹)) (nhdsWithin 0 (Set.Ioi 0)) (nhds 0) := by
          -- We'll use the fact that $\log(1 - u) \approx -u$ for $u$ close to $0$.
          have h_log_approx : Filter.Tendsto (fun u => Real.log (1 - u) / u) (nhdsWithin 0 (Set.Ioi 0)) (nhds (-1)) := by
            simpa [ div_eq_inv_mul ] using HasDerivAt.tendsto_slope_zero_right ( HasDerivAt.log ( hasDerivAt_id 0 |> HasDerivAt.const_sub 1 ) ( by norm_num ) );
          have h_log_approx : Filter.Tendsto (fun u => Real.log (1 - u) / (u * Real.log u⁻¹)) (nhdsWithin 0 (Set.Ioi 0)) (nhds 0) := by
            convert h_log_approx.div_atTop ( Real.tendsto_log_atTop.comp <| tendsto_inv_nhdsGT_zero ) using 2 ; norm_num [ div_mul_eq_div_div ];
            field_simp;
          convert h_log_approx.neg.mul ( Continuous.continuousWithinAt ( show Continuous fun u : ℝ => ( 1 - u ) by continuity ) ) using 2 <;> norm_num ; ring;
        simp_all +decide [ add_div ];
        exact le_trans ( Filter.Tendsto.add h_approx <| tendsto_const_nhds.congr' <| by filter_upwards [ ( Ioo_mem_nhdsGT_of_mem ⟨ le_rfl, zero_lt_one ⟩ ) ] with u hu using by rw [ div_self <| mul_ne_zero hu.1.ne' <| ne_of_lt <| Real.log_neg hu.1 hu.2 ] ) <| by norm_num;
      simpa [ mul_div_assoc ] using Filter.Tendsto.mul ( ContinuousAt.continuousWithinAt ( show ContinuousAt ( fun u : ℝ => ( 1 - u ) ^ ( k - 1 ) ) 0 by exact ContinuousAt.rpow ( continuousAt_const.sub continuousAt_id ) continuousAt_const <| Or.inl <| by linarith ) ) h_approx;
    · -- We'll use the fact that as $u \to 0$, $(1 - u)^k \approx 1 - ku$ and $\log(1 - (1 - u)^k) \approx \log(ku)$.
      have h_approx : Filter.Tendsto (fun u => (1 - (1 - u) ^ k) / u) (nhdsWithin 0 (Set.Ioi 0)) (nhds k) ∧ Filter.Tendsto (fun u => Real.log (1 - (1 - u) ^ k) / Real.log u) (nhdsWithin 0 (Set.Ioi 0)) (nhds 1) := by
        constructor;
        · simpa [ div_eq_inv_mul ] using HasDerivAt.tendsto_slope_zero_right ( HasDerivAt.const_sub 1 <| HasDerivAt.rpow ( hasDerivAt_id 0 |> HasDerivAt.const_sub 1 ) ( hasDerivAt_const _ k ) <| by norm_num );
        · -- We'll use the fact that $1 - (1 - u)^k \sim ku$ as $u \to 0$.
          have h_approx : Filter.Tendsto (fun u => (1 - (1 - u) ^ k) / u) (nhdsWithin 0 (Set.Ioi 0)) (nhds k) := by
            simpa [ div_eq_inv_mul ] using HasDerivAt.tendsto_slope_zero_right ( HasDerivAt.const_sub 1 <| HasDerivAt.rpow ( hasDerivAt_id 0 |> HasDerivAt.const_sub 1 ) ( hasDerivAt_const _ k ) <| by norm_num );
          -- We'll use the fact that $\log(1 - (1 - u)^k) \sim \log(ku)$ as $u \to 0$.
          have h_log_approx : Filter.Tendsto (fun u => Real.log (1 - (1 - u) ^ k) - Real.log u) (nhdsWithin 0 (Set.Ioi 0)) (nhds (Real.log k)) := by
            have := h_approx.log;
            exact this ( by positivity ) |> fun h => h.congr' ( by filter_upwards [ h_approx.eventually ( lt_mem_nhds <| show k > 0 by positivity ) ] with u hu using by rw [ Real.log_div ( by aesop ) ( by aesop ) ] );
          have h_log_approx : Filter.Tendsto (fun u => (Real.log (1 - (1 - u) ^ k) - Real.log u) / Real.log u) (nhdsWithin 0 (Set.Ioi 0)) (nhds 0) := by
            have h_log_approx : Filter.Tendsto (fun u => Real.log u) (nhdsWithin 0 (Set.Ioi 0)) Filter.atBot := by
              exact Real.tendsto_log_nhdsGT_zero;
            rw [ tendsto_zero_iff_norm_tendsto_zero ];
            simpa using Filter.Tendsto.div_atTop ( Filter.Tendsto.abs ‹Filter.Tendsto ( fun u : ℝ => Real.log ( 1 - ( 1 - u ) ^ k ) - Real.log u ) ( nhdsWithin 0 ( Set.Ioi 0 ) ) ( nhds ( Real.log k ) ) › ) ( Filter.tendsto_abs_atBot_atTop.comp h_log_approx );
          simpa using h_log_approx.add_const 1 |> Filter.Tendsto.congr' ( by filter_upwards [ ( Ioo_mem_nhdsGT_of_mem ⟨ le_rfl, zero_lt_one ⟩ ) ] with u hu using by rw [ sub_div, div_self <| ne_of_lt <| Real.log_neg hu.1 hu.2 ] ; ring );
      -- We'll use the fact that as $u \to 0$, $(1 - u)^k \approx 1 - ku$ and $\log(1 - u) \approx -u$ to simplify the expression.
      have h_approx : Filter.Tendsto (fun u => ((1 - u) ^ k * Real.log ((1 - u) ^ k)⁻¹) / (u * Real.log u⁻¹)) (nhdsWithin 0 (Set.Ioi 0)) (nhds 0) := by
        -- We'll use the fact that as $u \to 0$, $(1 - u)^k \approx 1 - ku$ and $\log(1 - u) \approx -u$ to simplify the expression. Hence, we can write:
        have h_approx : Filter.Tendsto (fun u => (1 - u) ^ k * k * Real.log (1 - u) / (u * Real.log u)) (nhdsWithin 0 (Set.Ioi 0)) (nhds 0) := by
          have h_approx : Filter.Tendsto (fun u => Real.log (1 - u) / u) (nhdsWithin 0 (Set.Ioi 0)) (nhds (-1)) := by
            simpa [ div_eq_inv_mul ] using HasDerivAt.tendsto_slope_zero_right ( HasDerivAt.log ( hasDerivAt_id 0 |> HasDerivAt.const_sub 1 ) ( by norm_num ) );
          have h_approx : Filter.Tendsto (fun u => (1 - u) ^ k * k * (Real.log (1 - u) / u) / Real.log u) (nhdsWithin 0 (Set.Ioi 0)) (nhds 0) := by
            have h_approx : Filter.Tendsto (fun u => (1 - u) ^ k * k * (Real.log (1 - u) / u)) (nhdsWithin 0 (Set.Ioi 0)) (nhds ((1 - 0) ^ k * k * (-1))) := by
              exact Filter.Tendsto.mul ( Filter.Tendsto.mul ( Filter.Tendsto.rpow ( tendsto_const_nhds.sub <| Filter.tendsto_id.mono_left inf_le_left ) tendsto_const_nhds <| Or.inl <| by linarith ) tendsto_const_nhds ) h_approx;
            have h_approx : Filter.Tendsto (fun u => Real.log u) (nhdsWithin 0 (Set.Ioi 0)) Filter.atBot := by
              exact Real.tendsto_log_nhdsGT_zero;
            rw [ tendsto_zero_iff_norm_tendsto_zero ];
            simpa using Filter.Tendsto.div_atTop ( Filter.Tendsto.norm ‹Filter.Tendsto ( fun u : ℝ => ( 1 - u ) ^ k * k * ( Real.log ( 1 - u ) / u ) ) ( nhdsWithin 0 ( Set.Ioi 0 ) ) ( nhds ( ( 1 - 0 ) ^ k * k * -1 ) ) › ) ( Filter.tendsto_abs_atBot_atTop.comp h_approx );
          exact h_approx.congr fun x => by rw [ mul_div_assoc ] ; ring;
        refine h_approx.congr' ( by filter_upwards [ ( Ioo_mem_nhdsGT_of_mem ⟨ le_rfl, zero_lt_one ⟩ ) ] with u hu using by simp +decide [ Real.log_rpow ( sub_pos.mpr hu.2 ), mul_assoc, mul_comm, mul_left_comm ] );
      convert h_approx.add ( ‹Filter.Tendsto ( fun u : ℝ => ( 1 - ( 1 - u ) ^ k ) / u ) ( nhdsWithin 0 ( Set.Ioi 0 ) ) ( nhds k ) ∧ Filter.Tendsto ( fun u : ℝ => Real.log ( 1 - ( 1 - u ) ^ k ) / Real.log u ) ( nhdsWithin 0 ( Set.Ioi 0 ) ) ( nhds 1 ) ›.1.mul ‹Filter.Tendsto ( fun u : ℝ => ( 1 - ( 1 - u ) ^ k ) / u ) ( nhdsWithin 0 ( Set.Ioi 0 ) ) ( nhds k ) ∧ Filter.Tendsto ( fun u : ℝ => Real.log ( 1 - ( 1 - u ) ^ k ) / Real.log u ) ( nhdsWithin 0 ( Set.Ioi 0 ) ) ( nhds 1 ) ›.2 ) using 2 <;> ring_nf;
      by_cases h : ‹ℝ› = 0 <;> simp +decide [ h, Real.log_inv ] ; ring;
  have := h_approx.1.div h_approx.2;
  exact this ( by positivity ) |> fun h => h.congr' ( by filter_upwards [ h_approx.1.eventually_ne one_ne_zero, h_approx.2.eventually_ne ( by positivity : ( k : ℝ ) ≠ 0 ) ] with u hu₁ hu₂ using by rw [ Pi.div_apply, div_div_div_cancel_right₀ ( by aesop ) ] )

/-
Given $M>0$, $0<a<1$, and a continuous function $f\colon[0,1]\to\mathbf R$ that is differentiable on $(0,1)$, suppose that $f(0)<M$, $f(a)=M$, $f(1)<M$, and $f'(x)=0$ iff $x=a$. Then $f(x)\le M$ with equality iff $x=a$.
-/
set_option maxHeartbeats 1000000 in
set_option maxRecDepth 4000 in
lemma lemma_l3 (M : ℝ) (a : ℝ) (f : ℝ → ℝ)
    (ha : 0 < a ∧ a < 1)
    (hf_cont : ContinuousOn f (Set.Icc 0 1))
    (h0 : f 0 < M) (ha_val : f a = M) (h1 : f 1 < M)
    (h_deriv : ∀ x ∈ Set.Ioo 0 1, deriv f x = 0 ↔ x = a) :
    ∀ x ∈ Set.Icc 0 1, f x ≤ M ∧ (f x = M ↔ x = a) := by
  -- By Fermat's theorem, $f'(c)=0$, so $c=a$.
  have h_fermat : ∀ c ∈ Set.Ioo 0 1, deriv f c = 0 → c = a := by
    aesop;
  have h_max : ∀ x ∈ Set.Icc 0 1, f x ≤ M := by
    -- By the Extreme Value Theorem, since $f$ is continuous on $[0,1]$, it attains a maximum at some $c \in [0,1]$.
    obtain ⟨c, hc⟩ : ∃ c ∈ Set.Icc 0 1, ∀ x ∈ Set.Icc 0 1, f x ≤ f c := by
      exact ( IsCompact.exists_isMaxOn ( CompactIccSpace.isCompact_Icc ) ⟨ a, Set.mem_Icc.mpr ⟨ by linarith, by linarith ⟩ ⟩ hf_cont ) |> fun ⟨ c, hc₁, hc₂ ⟩ => ⟨ c, hc₁, fun x hx => hc₂ hx ⟩;
    by_cases h_cases : c = 0 ∨ c = 1;
    · rcases h_cases with ( rfl | rfl ) <;> [ exact fun x hx => le_trans ( hc.2 x hx ) h0.le; exact fun x hx => le_trans ( hc.2 x hx ) h1.le ];
    · -- Since $c \in (0,1)$ and $f'(c) = 0$, by Fermat's theorem, we have $c = a$.
      have h_c_a : c = a := by
        exact h_fermat c ⟨ lt_of_le_of_ne hc.1.1 ( Ne.symm ( by tauto ) ), lt_of_le_of_ne hc.1.2 ( by tauto ) ⟩ ( IsLocalMax.deriv_eq_zero ( Filter.eventually_of_mem ( Icc_mem_nhds ( lt_of_le_of_ne hc.1.1 ( Ne.symm ( by tauto ) ) ) ( lt_of_le_of_ne hc.1.2 ( by tauto ) ) ) fun x hx => hc.2 x hx ) );
      grind;
  intros x hx;
  -- By the properties of the derivative, if $f(x) = M$ and $x \neq a$, then $f'(x) = 0$.
  by_cases hx_eq_a : x = a;
  · grind;
  · by_cases hx0 : x = 0 ∨ x = 1;
    · rcases hx0 with ( rfl | rfl ) <;> [ exact ⟨ by linarith, iff_of_false ( by linarith ) hx_eq_a ⟩ ; exact ⟨ by linarith, iff_of_false ( by linarith ) hx_eq_a ⟩ ];
    · exact ⟨ h_max x hx, iff_of_false ( fun h => hx_eq_a <| h_fermat x ⟨ lt_of_le_of_ne hx.1 <| Ne.symm <| by tauto, lt_of_le_of_ne hx.2 <| by tauto ⟩ <| IsLocalMax.deriv_eq_zero <| Filter.eventually_of_mem ( Ioo_mem_nhds ( lt_of_le_of_ne hx.1 <| Ne.symm <| by tauto ) ( lt_of_le_of_ne hx.2 <| by tauto ) ) fun y hy => by linarith [ h_max y <| Set.Ioo_subset_Icc_self hy ] ) hx_eq_a ⟩

/-
For $t > 0, t \ne 1$, $f(t) = \int_0^1 t^s ds$.
-/
noncomputable def f_aux (t : ℝ) : ℝ := (t - 1) / Real.log t

set_option maxHeartbeats 1000000 in
set_option maxRecDepth 4000 in
lemma lemma_f_integral (t : ℝ) (ht : t > 0) (ht1 : t ≠ 1) :
    f_aux t = ∫ s in (0 : ℝ)..1, t ^ s := by
  unfold f_aux;
  norm_num [ Real.rpow_def_of_pos ht ];
  rw [ intervalIntegral.integral_comp_mul_left ] <;> norm_num;
  · rw [ Real.exp_log ht, inv_mul_eq_div ];
  · exact ⟨ ht.ne', ht1, by linarith ⟩

/-
The derivative of $f(t) = \int_0^1 t^s ds$ is strictly decreasing on $(0, 1)$.
-/
noncomputable def f_int (t : ℝ) : ℝ := ∫ s in (0 : ℝ)..1, t ^ s

set_option maxHeartbeats 1000000 in
set_option maxRecDepth 4000 in
lemma f_int_deriv_decreasing : StrictAntiOn (deriv f_int) (Set.Ioo 0 1) := by
  -- By definition of $f_int$, we know that its derivative is $f'_int(t) = \int_0^1 s t^{s-1} ds$ for $t \in (0, 1)$.
  have h_deriv : ∀ t ∈ Set.Ioo (0 : ℝ) 1, deriv (fun t => ∫ s in (0 : ℝ)..1, t^s) t = ∫ s in (0 : ℝ)..1, s * t^(s - 1) := by
    intro t ht;
    apply HasDerivAt.deriv
    apply HasDerivAt.congr_of_eventuallyEq (f := fun y : ℝ => (y - 1) / Real.log y)
    · apply ((hasDerivAt_id t |>.sub (hasDerivAt_const t 1)).div
        (Real.hasDerivAt_log ht.1.ne') (Real.log_neg ht.1 ht.2).ne).congr_deriv
      symm
      rw [ intervalIntegral.integral_eq_sub_of_hasDerivAt ];
      rotate_right;
      use fun x => ( x * t ^ ( x - 1 ) ) / Real.log t - t ^ ( x - 1 ) / Real.log t ^ 2;
      · norm_num [ Real.rpow_neg_one ] ; ring_nf;
        simp +decide [ sq, mul_assoc, ht.1.ne' ];
        norm_num [ show Real.log t ≠ 0 by linarith [ Real.log_le_sub_one_of_pos ht.1, ht.2 ] ];
      · intro x hx
        have hd := (hasDerivAt_const x t).rpow ((hasDerivAt_id x).sub (hasDerivAt_const x 1)) ht.1
        apply ((((hasDerivAt_id x).mul hd).div_const (Real.log t)).sub
          (hd.div_const (Real.log t ^ 2))).congr_deriv
        simp only [Pi.sub_apply, id_eq, zero_mul, sub_zero, one_mul, zero_add]
        field_simp [(Real.log_neg ht.1 ht.2).ne, ht.1.ne'] <;> ring
      · exact Continuous.intervalIntegrable ( by exact Continuous.mul continuous_id ( Continuous.rpow continuous_const ( continuous_id.sub continuous_const ) <| by continuity ) ) _ _;
    · filter_upwards [Ioo_mem_nhds ht.1 ht.2] with y hy
      exact (lemma_f_integral y hy.1 hy.2.ne).symm
  -- By definition of $f_int$, we know that its derivative is $f'_int(t) = \int_0^1 s t^{s-1} ds$ for $t \in (0, 1)$. We need to show that this derivative is strictly decreasing.
  have h_deriv_decreasing : ∀ t1 t2 : ℝ, 0 < t1 → t1 < t2 → t2 < 1 → ∫ s in (0 : ℝ)..1, s * t1^(s - 1) > ∫ s in (0 : ℝ)..1, s * t2^(s - 1) := by
    intros t1 t2 ht1 ht2 ht2_lt_1
    have h_integral_lt : ∀ s ∈ Set.Ioo (0 : ℝ) 1, s * t1^(s - 1) > s * t2^(s - 1) := by
      exact fun s hs => mul_lt_mul_of_pos_left ( by rw [ Real.rpow_lt_rpow_iff_of_neg ] <;> linarith [ hs.1, hs.2 ] ) hs.1;
    apply lt_of_sub_pos;
    rw [ ← intervalIntegral.integral_sub ];
    · rw [ intervalIntegral.integral_of_le zero_le_one, MeasureTheory.integral_Ioc_eq_integral_Ioo ];
      rw [ MeasureTheory.integral_pos_iff_support_of_nonneg_ae ];
      · simp +zetaDelta at *;
        exact lt_of_lt_of_le ( by norm_num ) ( MeasureTheory.measure_mono <| show Set.Ioo 0 1 ⊆ ( Function.support fun t : ℝ => t * t1 ^ ( t - 1 ) - t * t2 ^ ( t - 1 ) ) ∩ Set.Ioo 0 1 from fun x hx => ⟨ ne_of_gt <| sub_pos.mpr <| h_integral_lt x hx.1 hx.2, hx ⟩ );
      · filter_upwards [ MeasureTheory.ae_restrict_mem measurableSet_Ioo ] with s hs using sub_nonneg_of_le <| le_of_lt <| h_integral_lt s hs;
      · exact ContinuousOn.integrableOn_Icc ( by exact continuousOn_of_forall_continuousAt fun x hx => by exact ContinuousAt.sub ( ContinuousAt.mul continuousAt_id <| ContinuousAt.rpow continuousAt_const ( continuousAt_id.sub continuousAt_const ) <| Or.inl <| by linarith ) <| ContinuousAt.mul continuousAt_id <| ContinuousAt.rpow continuousAt_const ( continuousAt_id.sub continuousAt_const ) <| Or.inl <| by linarith ) |> fun h => h.mono_set <| Set.Ioo_subset_Icc_self;
    · exact ContinuousOn.intervalIntegrable ( by exact continuousOn_of_forall_continuousAt fun x hx => by exact ContinuousAt.mul continuousAt_id <| ContinuousAt.rpow continuousAt_const ( continuousAt_id.sub continuousAt_const ) <| Or.inl <| by linarith );
    · exact ContinuousOn.intervalIntegrable ( by exact continuousOn_of_forall_continuousAt fun x hx => by exact ContinuousAt.mul continuousAt_id <| ContinuousAt.rpow continuousAt_const ( continuousAt_id.sub continuousAt_const ) <| Or.inl <| by linarith );
  intros t1 ht1 t2 ht2 hltop;
  convert h_deriv_decreasing t1 t2 ht1.1 hltop ht2.2 |> lt_of_lt_of_le <| le_rfl using 1 <;> aesop

/-
For $x \in (0, 1)$, $1/G(x) = f(x) + f(1-x)$ where $f(t) = \int_0^1 t^s ds$.
-/
noncomputable def G (x : ℝ) : ℝ := Real.log x * Real.log (1 - x) / Real.binEntropy x

set_option maxHeartbeats 1000000 in
set_option maxRecDepth 4000 in
lemma one_div_G_eq (x : ℝ) (hx : 0 < x ∧ x < 1) :
    1 / G x = f_int x + f_int (1 - x) := by
  unfold G f_int;
  norm_num [ Real.rpow_def_of_pos hx.1, Real.rpow_def_of_pos ( sub_pos.2 hx.2 ), mul_comm ];
  rw [ intervalIntegral.integral_comp_mul_right, intervalIntegral.integral_comp_mul_right ] <;> norm_num [ Real.log_pow, hx.1.ne', hx.2.ne' ];
  · rw [ Real.exp_log hx.1, Real.exp_log ( by linarith ) ] ; unfold Real.binEntropy ; ring_nf;
    rw [ Real.log_inv, Real.log_inv ] ; ring_nf;
    simpa [ show Real.log x ≠ 0 from ne_of_lt ( Real.log_neg hx.1 hx.2 ), show Real.log ( 1 - x ) ≠ 0 from ne_of_lt ( Real.log_neg ( by linarith ) ( by linarith ) ) ] using by ring;
  · constructor <;> linarith;
  · constructor <;> linarith

/-
For $x \in (0, 1)$, $1/G(x) = f(x) + f(1-x)$ where $f(t) = \int_0^1 t^s ds$.
-/
noncomputable def BoppanaG (x : ℝ) : ℝ := Real.log x * Real.log (1 - x) / Real.binEntropy x

set_option maxHeartbeats 1000000 in
set_option maxRecDepth 4000 in
lemma one_div_BoppanaG_eq (x : ℝ) (hx : 0 < x ∧ x < 1) :
    1 / BoppanaG x = f_int x + f_int (1 - x) := by
  exact one_div_G_eq x hx

/-
$1/BoppanaG$ is strictly increasing on $(0, 1/2)$.
-/
set_option maxHeartbeats 1000000 in
set_option maxRecDepth 4000 in
lemma one_div_BoppanaG_strictMonoOn : StrictMonoOn (fun x => 1 / BoppanaG x) (Set.Ioo 0 (1 / 2)) := by
  -- The derivative of $1/BoppanaG$ is $f_int'(x) - f_int'(1-x)$.
  have h_deriv : ∀ x ∈ Set.Ioo 0 (1 / 2), deriv (fun x => 1 / BoppanaG x) x = deriv f_int x - deriv f_int (1 - x) := by
    intro x hx;
    rw [ show deriv ( fun x => 1 / BoppanaG x ) x = deriv ( fun x => f_int x + f_int ( 1 - x ) ) x by exact Filter.EventuallyEq.deriv_eq <| Filter.eventuallyEq_of_mem ( Ioo_mem_nhds hx.1 hx.2 ) fun y hy => one_div_BoppanaG_eq y ⟨ hy.1, by linarith [ hy.2 ] ⟩ ];
    convert HasDerivAt.deriv ( HasDerivAt.add ( hasDerivAt_deriv_iff.mpr ?_ ) ( HasDerivAt.comp x ( hasDerivAt_deriv_iff.mpr ?_ ) ( hasDerivAt_id' x |> HasDerivAt.const_sub 1 ) ) ) using 1 <;> norm_num;
    congr! 1;
    exact (Set.eqOn_univ (fun x ↦ f_int x + f_int (1 - x)) (f_int + f_int ∘ fun x ↦ 1 - x)).mp fun ⦃x⦄ a ↦
    congrArg (HAdd.hAdd (f_int x)) (congrFun rfl (1 - x));
    · ring;
    · -- The integral of $t^s$ with respect to $s$ is $\frac{t^s}{\log t}$, so $f_int(x) = \frac{x - 1}{\log x}$.
      have h_f_int : ∀ x ∈ Set.Ioo 0 1, f_int x = (x - 1) / Real.log x := by
        intro x hx; rw [ f_int ] ; rw [ intervalIntegral.integral_congr fun s hs => by rw [ Real.rpow_def_of_pos hx.1 ] ] ; norm_num [ div_eq_mul_inv, intervalIntegral.integral_comp_mul_left, hx.1.ne', hx.2.ne' ] ;
        rw [ intervalIntegral.integral_comp_mul_left ] <;> norm_num [ hx.1.ne', hx.2.ne' ];
        · rw [ Real.exp_log hx.1, mul_comm ];
        · constructor <;> linarith [ hx.1, hx.2 ];
      exact DifferentiableAt.congr_of_eventuallyEq ( show DifferentiableAt ℝ ( fun x => ( x - 1 ) / Real.log x ) x from DifferentiableAt.div ( differentiableAt_id.sub_const _ ) ( Real.differentiableAt_log hx.1.ne' ) ( ne_of_lt ( Real.log_neg hx.1 ( by linarith [ hx.2 ] ) ) ) ) ( Filter.eventuallyEq_of_mem ( Ioo_mem_nhds hx.1 ( by linarith [ hx.2 ] ) ) fun y hy => h_f_int y hy );
    · have h_diff : ∀ t ∈ Set.Ioo 0 1, DifferentiableAt ℝ f_int t := by
        intro t ht;
        have h_diff : DifferentiableAt ℝ (fun t => ∫ s in (0 : ℝ)..1, t ^ s) t := by
          have h_int : ∀ t ∈ Set.Ioo 0 1, ∫ s in (0 : ℝ)..1, t ^ s = (t - 1) / Real.log t := by
            intro t ht; norm_num [ Real.rpow_def_of_pos ht.1 ];
            rw [ intervalIntegral.integral_comp_mul_left ] <;> norm_num [ ht.1.ne', ht.2.ne ];
            · rw [ Real.exp_log ht.1, inv_mul_eq_div ];
            · linarith [ ht.1, ht.2 ]
          exact DifferentiableAt.congr_of_eventuallyEq ( show DifferentiableAt ℝ ( fun t => ( t - 1 ) / Real.log t ) t from DifferentiableAt.div ( differentiableAt_id.sub_const _ ) ( Real.differentiableAt_log ht.1.ne' ) ( ne_of_lt ( Real.log_neg ht.1 ht.2 ) ) ) ( Filter.eventuallyEq_of_mem ( Ioo_mem_nhds ht.1 ht.2 ) fun x hx => h_int x hx );
        exact h_diff;
      exact h_diff _ ⟨ by linarith [ hx.1, hx.2 ], by linarith [ hx.1, hx.2 ] ⟩;
  -- Since $f_int'$ is strictly decreasing on $(0, 1)$, $f_int'(x) > f_int'(1-x)$ for $x \in (0, 1/2)$.
  have h_deriv_pos : ∀ x ∈ Set.Ioo 0 (1 / 2), deriv f_int x > deriv f_int (1 - x) := by
    exact fun x hx => f_int_deriv_decreasing ⟨ by linarith [ hx.1, hx.2 ], by linarith [ hx.1, hx.2 ] ⟩ ⟨ by linarith [ hx.1, hx.2 ], by linarith [ hx.1, hx.2 ] ⟩ ( by linarith [ hx.1, hx.2 ] );
  intro x hx y hy hxy;
  -- By the Mean Value Theorem, there exists some $c \in (x, y)$ such that $f'(c) = (f(y) - f(x)) / (y - x)$.
  obtain ⟨c, hc⟩ : ∃ c ∈ Set.Ioo x y, deriv (fun x => 1 / BoppanaG x) c = (1 / BoppanaG y - 1 / BoppanaG x) / (y - x) := by
    apply_rules [ exists_deriv_eq_slope ];
    · refine' continuousOn_of_forall_continuousAt fun z hz => ContinuousAt.div continuousAt_const _ _;
      · refine' ContinuousAt.div _ _ _ <;> norm_num;
        · exact ContinuousAt.mul ( Real.continuousAt_log ( by linarith [ hx.1, hy.1, hz.1 ] ) ) ( ContinuousAt.log ( continuousAt_const.sub continuousAt_id ) ( by linarith [ hx.2, hy.2, hz.2 ] ) );
        · refine' ContinuousAt.add _ _;
          · exact ContinuousAt.mul continuousAt_id ( ContinuousAt.log ( continuousAt_id.inv₀ <| ne_of_gt <| lt_of_lt_of_le hx.1 hz.1 ) <| ne_of_gt <| inv_pos.mpr <| lt_of_lt_of_le hx.1 hz.1 );
          · exact ContinuousAt.mul ( continuousAt_const.sub continuousAt_id ) ( ContinuousAt.log ( ContinuousAt.inv₀ ( continuousAt_const.sub continuousAt_id ) ( by linarith [ hx.1, hx.2, hy.1, hy.2, hz.1, hz.2 ] ) ) ( by exact ne_of_gt ( inv_pos.mpr ( by linarith [ hx.1, hx.2, hy.1, hy.2, hz.1, hz.2 ] ) ) ) );
        · norm_num [ Real.binEntropy ];
          nlinarith [ hx.1, hx.2, hy.1, hy.2, hz.1, hz.2, Real.log_le_sub_one_of_pos ( show 0 < z by linarith [ hx.1, hz.1 ] ), Real.log_le_sub_one_of_pos ( show 0 < 1 - z by linarith [ hy.2, hz.2 ] ) ];
      · unfold BoppanaG;
        norm_num [ Real.binEntropy ];
        exact ⟨ ⟨ ⟨ by linarith [ hx.1, hy.1, hz.1 ], by linarith [ hx.2, hy.2, hz.2 ], by linarith [ hx.1, hy.1, hz.1 ] ⟩, by linarith [ hx.2, hy.2, hz.2 ], by linarith [ hx.1, hy.1, hz.1 ], by linarith [ hx.2, hy.2, hz.2 ] ⟩, by nlinarith [ hx.1, hy.1, hz.1, hx.2, hy.2, hz.2, Real.log_le_sub_one_of_pos ( by linarith [ hx.1, hy.1, hz.1 ] : 0 < z ), Real.log_le_sub_one_of_pos ( by linarith [ hx.2, hy.2, hz.2 ] : 0 < 1 - z ) ] ⟩;
    · exact fun z hz => DifferentiableAt.differentiableWithinAt ( by exact differentiableAt_of_deriv_ne_zero ( by rw [ h_deriv z ⟨ by linarith [ hx.1, hy.1, hz.1 ], by linarith [ hx.2, hy.2, hz.2 ] ⟩ ] ; linarith [ h_deriv_pos z ⟨ by linarith [ hx.1, hy.1, hz.1 ], by linarith [ hx.2, hy.2, hz.2 ] ⟩ ] ) );
  have := h_deriv c ⟨ by linarith [ hc.1.1, hx.1 ], by linarith [ hc.1.2, hy.2 ] ⟩ ; have := h_deriv_pos c ⟨ by linarith [ hc.1.1, hx.1 ], by linarith [ hc.1.2, hy.2 ] ⟩ ; rw [ eq_div_iff ] at hc <;> nlinarith;

/-
`BoppanaG` is strictly decreasing on $(0, 1/2)$.
-/
set_option maxHeartbeats 1000000 in
set_option maxRecDepth 4000 in
lemma BoppanaG_strictAntiOn_Ioo : StrictAntiOn BoppanaG (Set.Ioo 0 (1 / 2)) := by
  -- Since $BoppanaG(x) > 0$ for $x \in (0, 1/2)$, the function $y \mapsto 1/y$ is strictly decreasing on the range of $BoppanaG$.
  have h_BoppanaG_pos : ∀ x : ℝ, 0 < x ∧ x < 1 / 2 → 0 < BoppanaG x := by
    unfold BoppanaG;
    norm_num [ Real.binEntropy ];
    exact fun x hx₁ hx₂ => div_pos ( mul_pos_of_neg_of_neg ( Real.log_neg hx₁ ( by linarith ) ) ( Real.log_neg ( by linarith ) ( by linarith ) ) ) ( by nlinarith [ Real.log_le_sub_one_of_pos hx₁, Real.log_le_sub_one_of_pos ( by linarith : 0 < 1 - x ) ] );
  intro x hx y hy hxy;
  have := one_div_BoppanaG_strictMonoOn hx hy hxy; rw [ div_lt_div_iff₀ ] at this <;> linarith [ h_BoppanaG_pos x hx, h_BoppanaG_pos y hy ] ;

/-
Suppose $x^k=1-x$. Then $x=1/(1+\alpha_k)$.
-/
set_option maxHeartbeats 1000000 in
set_option maxRecDepth 4000 in
lemma lemma_l5 (k : ℝ) (hk : k > 1) (x : ℝ) (hx : 0 < x ∧ x < 1) (h_eq : x ^ k = 1 - x) :
    x = 1 / (1 + alpha k) := by
  -- By definition of $alpha_k$, we know that $alpha_k = \frac{1 - x}{x}$.
  have h_alpha : alpha k = (1 - x) / x := by
    -- By definition of $alpha_k$, we know that $alpha_k$ is the unique solution to $x(1+x)^{k-1}=1$ in $(0, 1)$.
    have h_alpha_unique : ∀ x > 0, x * (1 + x) ^ (k - 1) = 1 → x = alpha k := by
      intro x hx_pos hx_eq
      have h_unique : ∀ y > 0, y * (1 + y) ^ (k - 1) = 1 → y = x := by
        intros y hy_pos hy_eq
        have h_unique : StrictMonoOn (fun x : ℝ => x * (1 + x) ^ (k - 1)) (Set.Ioi 0) := by
          exact fun x hx y hy hxy => mul_lt_mul'' hxy ( Real.rpow_lt_rpow ( by linarith [ hx.out ] ) ( by linarith [ hx.out, hy.out ] ) ( by linarith ) ) ( by linarith [ hx.out, hy.out ] ) ( by exact Real.rpow_nonneg ( by linarith [ hx.out, hy.out ] ) _ );
        exact StrictMonoOn.injOn h_unique hy_pos hx_pos <| by linarith;
      unfold alpha;
      have := Classical.choose_spec ( show ∃ x : ℝ, x > 0 ∧ x * ( 1 + x ) ^ ( k - 1 ) = 1 from ⟨ x, hx_pos, hx_eq ⟩ ) ; specialize h_unique _ this.1 this.2; aesop;
    rw [ ← h_alpha_unique ( ( 1 - x ) / x ) ( div_pos ( by linarith ) hx.1 ) ];
    rw [ show ( 1 + ( 1 - x ) / x ) = ( 1 / x ) by rw [ add_div' ] <;> norm_num ; linarith ];
    rw [ Real.div_rpow ] <;> norm_num <;> try linarith;
    rw [ ← h_eq, Real.rpow_sub hx.1, Real.rpow_one ] ; ring_nf ; norm_num [ hx.1.ne' ];
    nlinarith [ mul_inv_cancel₀ hx.1.ne', mul_inv_cancel₀ ( ne_of_gt ( Real.rpow_pos_of_pos hx.1 k ) ) ];
  grind

/-
We have $\lim_{x\to 0^+}q(x)=\lim_{x\to1^-}q(x)=1/k$.
-/
set_option maxHeartbeats 1000000 in
set_option maxRecDepth 4000 in
lemma lemma_l1 (k : ℝ) (hk : k > 1) :
    Filter.Tendsto (q k) (nhdsWithin 0 (Set.Ioi 0)) (nhds (1 / k)) ∧
    Filter.Tendsto (q k) (nhdsWithin 1 (Set.Iio 1)) (nhds (1 / k)) := by
  exact ⟨lemma_l1_zero k hk, lemma_l1_one k hk⟩

/-
$BoppanaG(1-x)=BoppanaG(x)$.
-/
set_option maxHeartbeats 1000000 in
set_option maxRecDepth 4000 in
lemma BoppanaG_symm (x : ℝ) : BoppanaG (1 - x) = BoppanaG x := by
  unfold BoppanaG;
  unfold Real.binEntropy; ring_nf;

/-
`BoppanaG` is strictly decreasing on $(0, 1/2]$.
-/
set_option maxHeartbeats 1000000 in
set_option maxRecDepth 4000 in
lemma BoppanaG_strictAntiOn_Ioc : StrictAntiOn BoppanaG (Set.Ioc 0 (1 / 2)) := by
  -- We already know `BoppanaG` is strictly decreasing on $(0, 1/2)$.
  have h_l6 : StrictAntiOn BoppanaG (Set.Ioo 0 (1 / 2)) := by
    exact BoppanaG_strictAntiOn_Ioo;
  -- Since `BoppanaG` is continuous at $1/2$, the strict decrease extends to $(0, 1/2]$.
  have h_cont : Filter.Tendsto (fun x => BoppanaG x) (nhdsWithin (1 / 2) (Set.Iio (1 / 2))) (nhds (BoppanaG (1 / 2))) := by
    refine' Filter.Tendsto.mono_left _ nhdsWithin_le_nhds;
    refine' ContinuousAt.div _ _ _ <;> norm_num [ Real.binEntropy ];
    · exact ContinuousAt.mul ( Real.continuousAt_log ( by norm_num ) ) ( ContinuousAt.log ( continuousAt_const.sub continuousAt_id ) ( by norm_num ) );
    · refine' ContinuousAt.add _ _ <;> norm_num [ Real.binEntropy ];
      · exact ContinuousAt.neg ( ContinuousAt.mul continuousAt_id ( Real.continuousAt_log ( by norm_num ) ) );
      · exact ContinuousAt.neg ( ContinuousAt.mul ( continuousAt_const.sub continuousAt_id ) ( ContinuousAt.log ( continuousAt_const.sub continuousAt_id ) ( by norm_num ) ) );
  -- For any $x \in (0, 1/2)$, $BoppanaG(x) > \lim_{t \to 1/2^-} BoppanaG(t) = BoppanaG(1/2)$.
  have h_lim : ∀ x ∈ Set.Ioo 0 (1 / 2), BoppanaG x > BoppanaG (1 / 2) := by
    intro x hx;
    refine' lt_of_le_of_lt _ ( h_l6 ⟨ hx.1, hx.2 ⟩ ⟨ show 0 < ( x + 1 / 2 ) / 2 by linarith [ hx.1 ], show ( x + 1 / 2 ) / 2 < 1 / 2 by linarith [ hx.2 ] ⟩ ( show x < ( x + 1 / 2 ) / 2 by linarith [ hx.1, hx.2 ] ) );
    refine' le_of_tendsto h_cont _;
    filter_upwards [ Ioo_mem_nhdsLT ( show ( x + 1 / 2 ) / 2 < 1 / 2 by linarith [ hx.2 ] ) ] with y hy using h_l6.le_iff_ge ( by constructor <;> linarith [ hy.1, hy.2, hx.1, hx.2 ] ) ( by constructor <;> linarith [ hy.1, hy.2, hx.1, hx.2 ] ) |>.2 hy.1.le;
  intro x hx y hy hxy;
  cases eq_or_lt_of_le hx.2 <;> cases eq_or_lt_of_le hy.2 <;> first | linarith | aesop

/-
$BoppanaG(x)=BoppanaG(y) \iff x=y \lor x=1-y$ for $x,y \in (0,1)$.
-/
set_option maxHeartbeats 1000000 in
set_option maxRecDepth 4000 in
lemma BoppanaG_eq_iff (x y : ℝ) (hx : 0 < x ∧ x < 1) (hy : 0 < y ∧ y < 1) :
    BoppanaG x = BoppanaG y ↔ x = y ∨ x = 1 - y := by
  constructor <;> intro hxy;
  · -- Assume w.l.o.g. $x \le 1/2$.
    suffices h_wlog : ∀ {x y : ℝ}, 0 < x → x < 1 → 0 < y → y < 1 → x ≤ 1 / 2 → BoppanaG x = BoppanaG y → x = y ∨ x = 1 - y by
      by_cases hx2 : x ≤ 1 / 2;
      · exact h_wlog hx.1 hx.2 hy.1 hy.2 hx2 hxy;
      · contrapose! h_wlog;
        use 1 - x, 1 - y;
        exact ⟨ by linarith, by linarith, by linarith, by linarith, by linarith, by simpa [ BoppanaG_symm ] using hxy, by aesop ⟩;
    intros x y hx hy hx' hy' hxy h_eq
    by_cases hy'' : y ≤ 1 / 2;
    · -- Since $BoppanaG$ is strictly decreasing on $(0, 1/2]$, it is injective there.
      have h_inj : StrictAntiOn BoppanaG (Set.Ioc 0 (1 / 2)) := by
        exact BoppanaG_strictAntiOn_Ioc;
      exact Or.inl <| StrictAntiOn.injOn h_inj ⟨ hx, hxy ⟩ ⟨ hx', hy'' ⟩ h_eq;
    · -- Since $y > 1/2$, we have $1 - y \in (0, 1/2)$. By the symmetry of $BoppanaG$, we have $BoppanaG(y) = BoppanaG(1 - y)$.
      have h_symm : BoppanaG y = BoppanaG (1 - y) := by
        exact Eq.symm (BoppanaG_symm y);
      have h_inj : StrictAntiOn BoppanaG (Set.Ioc 0 (1 / 2)) := by
        exact BoppanaG_strictAntiOn_Ioc;
      exact Or.inr <| StrictAntiOn.injOn h_inj ⟨ by linarith, by linarith ⟩ ⟨ by linarith, by linarith ⟩ <| by linarith;
  · cases hxy <;> simp +decide [ *, BoppanaG_symm ]

/-
$q'(x)=0 \iff BoppanaG(x)=BoppanaG(x^k)$ for $x \in (0, 1)$.
-/
set_option maxHeartbeats 1000000 in
set_option maxRecDepth 4000 in
lemma q_deriv_eq_zero_iff (k : ℝ) (hk : k > 1) (x : ℝ) (hx : 0 < x ∧ x < 1) :
    deriv (q k) x = 0 ↔ BoppanaG x = BoppanaG (x ^ k) := by
  -- By definition of $q$, we know that $q'(x)=0 \iff ((k-1)h(x) + xh'(x))h(x^k) = kx^k h(x) h'(x^k)$.
  have h_eq : deriv (q k) x = 0 ↔ ((k - 1) * Real.binEntropy x + x * deriv Real.binEntropy x) * Real.binEntropy (x ^ k) = k * x ^ k * Real.binEntropy x * deriv Real.binEntropy (x ^ k) := by
    have h_eq : deriv (q k) x = ((k - 1) * x ^ (k - 2) * Real.binEntropy x + x ^ (k - 1) * deriv Real.binEntropy x) * Real.binEntropy (x ^ k) / Real.binEntropy (x ^ k) ^ 2 - x ^ (k - 1) * Real.binEntropy x * k * x ^ (k - 1) * deriv Real.binEntropy (x ^ k) / Real.binEntropy (x ^ k) ^ 2 := by
      have hxk₀ := Real.rpow_pos_of_pos hx.1 k
      have hxk₁ := Real.rpow_lt_one hx.1.le hx.2 (by linarith : 0 < k)
      have hn := (Real.hasDerivAt_rpow_const (p := k-1) (Or.inl hx.1.ne')).mul
        (Real.differentiableAt_binEntropy hx.1.ne' hx.2.ne).hasDerivAt
      have hd := (Real.differentiableAt_binEntropy hxk₀.ne' hxk₁.ne).hasDerivAt.comp x
        (Real.hasDerivAt_rpow_const (p := k) (Or.inl hx.1.ne'))
      rw [show deriv (q k) x = _ from (hn.div hd (Real.binEntropy_pos hxk₀ hxk₁).ne').deriv]
      rw [show k - 2 = k - 1 - 1 by ring]
      simp only [Function.comp_apply, Pi.mul_apply]
      ring
    rw [ h_eq, div_sub_div_same, div_eq_iff ];
    · rw [ show k - 2 = k - 1 - 1 by ring, Real.rpow_sub_one hx.1.ne', Real.rpow_sub_one hx.1.ne' ] ; ring_nf;
      field_simp;
      rw [ div_eq_iff ( pow_ne_zero 2 hx.1.ne' ) ] ; constructor <;> intro <;> nlinarith [ Real.rpow_pos_of_pos hx.1 k ] ;
    · simp +zetaDelta at *;
      unfold Real.binEntropy;
      rw [ Real.log_inv, Real.log_inv ];
      nlinarith [ Real.log_le_sub_one_of_pos ( show 0 < x ^ k by exact Real.rpow_pos_of_pos hx.1 _ ), Real.log_le_sub_one_of_pos ( show 0 < 1 - x ^ k by exact sub_pos.mpr ( Real.rpow_lt_one hx.1.le hx.2 ( by linarith ) ) ), Real.rpow_pos_of_pos hx.1 k, Real.rpow_lt_one hx.1.le hx.2 ( by linarith : 0 < k ) ];
  -- Using $xh'(x) = h(x) + \log(1-x)$ and $x^k h'(x^k) = h(x^k) + \log(1-x^k)$, we get
  have h_log : deriv Real.binEntropy x = (Real.binEntropy x + Real.log (1 - x)) / x ∧ deriv Real.binEntropy (x ^ k) = (Real.binEntropy (x ^ k) + Real.log (1 - x ^ k)) / (x ^ k) := by
    have h_log : ∀ x ∈ Set.Ioo 0 1, deriv Real.binEntropy x = (Real.binEntropy x + Real.log (1 - x)) / x := by
      intro x hx
      rw [Real.deriv_binEntropy, eq_div_iff hx.1.ne']
      simp only [Real.binEntropy, Real.log_inv]
      ring
    exact ⟨ h_log x hx, h_log ( x ^ k ) ⟨ Real.rpow_pos_of_pos hx.1 _, Real.rpow_lt_one hx.1.le hx.2 ( by positivity ) ⟩ ⟩;
  simp_all +decide [ mul_div_cancel₀, ne_of_gt ];
  norm_num [ BoppanaG, mul_assoc, mul_div_cancel₀ _ ( ne_of_gt ( Real.rpow_pos_of_pos hx.1 k ) ) ];
  by_cases h : Real.binEntropy x = 0 <;> by_cases h' : Real.binEntropy ( x ^ k ) = 0 <;> simp_all +decide [ Real.log_rpow hx.1, mul_assoc, ne_of_gt ( Real.rpow_pos_of_pos hx.1 _ ) ];
  · norm_num [ Real.binEntropy ] at *;
    exact absurd h ( by nlinarith [ Real.log_le_sub_one_of_pos hx.1, Real.log_le_sub_one_of_pos ( by linarith : 0 < 1 - x ) ] );
  · unfold Real.binEntropy at *;
    simp_all +decide [ Real.log_inv, Real.rpow_def_of_pos hx.1 ];
    contrapose! h';
    exact ne_of_gt ( add_pos_of_pos_of_nonneg ( neg_pos_of_neg ( mul_neg_of_pos_of_neg ( Real.exp_pos _ ) ( mul_neg_of_neg_of_pos ( Real.log_neg hx.1 hx.2 ) ( by linarith ) ) ) ) ( neg_nonneg_of_nonpos ( mul_nonpos_of_nonneg_of_nonpos ( sub_nonneg.mpr ( Real.exp_le_one_iff.mpr ( by nlinarith [ Real.log_le_sub_one_of_pos hx.1 ] ) ) ) ( Real.log_nonpos ( sub_nonneg.mpr ( Real.exp_le_one_iff.mpr ( by nlinarith [ Real.log_le_sub_one_of_pos hx.1 ] ) ) ) ( sub_le_self _ ( Real.exp_nonneg _ ) ) ) ) ) );
  · field_simp;
    rw [ eq_div_iff ( ne_of_gt ( Real.rpow_pos_of_pos hx.1 _ ) ) ] ; ring_nf;
    constructor <;> intro <;> nlinarith [ Real.log_le_sub_one_of_pos hx.1, Real.log_pos ( show 1 < k by linarith ), Real.rpow_pos_of_pos hx.1 k ]

/-
$q(1/(1+\alpha_k)) = \alpha_k$.
-/
set_option maxHeartbeats 1000000 in
set_option maxRecDepth 4000 in
lemma lemma_q_alpha (k : ℝ) (hk : k > 1) :
    q k (1 / (1 + alpha k)) = alpha k := by
  unfold q
  have hα : 0 < alpha k := alpha_pos k hk
  have h1α : 0 < 1 + alpha k := by linarith
  have h_alpha : alpha k = 1 / (1 + alpha k) ^ (k - 1) := by
    refine (eq_div_iff ?_).2 ?_
    · exact (Real.rpow_pos_of_pos h1α _).ne'
    · simpa [mul_comm] using (alpha_spec k hk).2
  have h_alpha_inv : (1 / (1 + alpha k)) ^ (k - 1) = alpha k := by
    rw [Real.div_rpow]
    · simpa [Real.one_rpow] using h_alpha.symm
    · norm_num
    · exact h1α.le
  rw [show (1 / (1 + alpha k)) ^ k = (1 / (1 + alpha k)) ^ (k - 1) * (1 / (1 + alpha k)) by
        rw [← Real.rpow_add_one (one_div_ne_zero (by linarith))]
        ring_nf, h_alpha_inv]
  field_simp
  rw [div_eq_iff]
  · unfold Real.binEntropy
    field_simp
    grind
  · have hx0 : 0 < alpha k / (1 + alpha k) := by
      exact div_pos hα h1α
    have hx1 : alpha k / (1 + alpha k) < 1 := by
      exact (div_lt_one h1α).2 (by linarith)
    exact (Real.binEntropy_pos hx0 hx1).ne'

/-
Let $k>1$ be real. Then $\alpha_k h(x^k)\ge x^{k-1}h(x)$ for $0\le x\le1$.
-/
set_option maxHeartbeats 1000000 in
set_option maxRecDepth 4000 in
theorem generalized_boppana (k : ℝ) (hk : k > 1) (x : ℝ) (hx : 0 ≤ x ∧ x ≤ 1) :
    alpha k * Real.binEntropy (x ^ k) ≥ x ^ (k - 1) * Real.binEntropy x := by
  -- Since $q(x)$ is continuous on $(0, 1)$ and tends to $1/k$ at endpoints (Lemma 1), we can extend $q$ to $[0, 1]$ by setting $q(0)=q(1)=1/k$.
  set q_ext : ℝ → ℝ := fun x => if x = 0 ∨ x = 1 then 1 / k else q k x
  have hq_ext_continuous : ContinuousOn q_ext (Set.Icc 0 1) := by
    -- By definition of $q_ext$, we know that it is continuous on $(0, 1)$ and tends to $1/k$ at endpoints.
    have hq_ext_cont : ContinuousOn (fun x => if x = 0 ∨ x = 1 then 1 / k else q k x) (Set.Icc 0 1) := by
      have h_cont_at_0 : Filter.Tendsto (q k) (nhdsWithin 0 (Set.Ioi 0)) (nhds (1 / k)) := by
        exact lemma_l1_zero k hk
      have h_cont_at_1 : Filter.Tendsto (q k) (nhdsWithin 1 (Set.Iio 1)) (nhds (1 / k)) := by
        convert lemma_l1_one k hk using 1
      intro x hx; by_cases hx0 : x = 0 <;> by_cases hx1 : x = 1 <;> simp_all +decide [ ContinuousWithinAt ] ;
      · rw [ Metric.tendsto_nhdsWithin_nhds ] at *;
        intro ε hε; rcases h_cont_at_0 ε hε with ⟨ δ, hδ, H ⟩ ; use δ, hδ; intro x hx₁ hx₂; cases eq_or_lt_of_le hx₁.out <;> aesop;
      · rw [ Metric.tendsto_nhdsWithin_nhds ] at *;
        intro ε hε; rcases h_cont_at_1 ε hε with ⟨ δ, hδ, H ⟩ ; use δ, hδ; intro x hx₁ hx₂; cases eq_or_lt_of_le hx₁.out <;> aesop;
      · refine' Filter.Tendsto.congr' _ _;
        use fun x => q k x;
        · filter_upwards [ eventually_nhdsWithin_of_eventually_nhds ( isOpen_compl_singleton.mem_nhds hx0 ), eventually_nhdsWithin_of_eventually_nhds ( isOpen_compl_singleton.mem_nhds hx1 ) ] with y hy0 hy1 using by aesop;
        · refine' Filter.Tendsto.mono_left _ nhdsWithin_le_nhds;
          refine' ContinuousAt.div _ _ _ <;> norm_num [ Real.binEntropy ];
          · exact ContinuousAt.mul ( ContinuousAt.rpow continuousAt_id continuousAt_const <| Or.inl hx0 ) <| ContinuousAt.add ( ContinuousAt.neg <| ContinuousAt.mul continuousAt_id <| Real.continuousAt_log hx0 ) <| ContinuousAt.neg <| ContinuousAt.mul ( continuousAt_const.sub continuousAt_id ) <| ContinuousAt.log ( continuousAt_const.sub continuousAt_id ) <| by contrapose! hx1; linarith;
          · refine' ContinuousAt.add _ _;
            · exact ContinuousAt.neg ( ContinuousAt.mul ( ContinuousAt.rpow continuousAt_id continuousAt_const <| Or.inl hx0 ) <| ContinuousAt.log ( ContinuousAt.rpow continuousAt_id continuousAt_const <| Or.inl hx0 ) <| ne_of_gt <| Real.rpow_pos_of_pos ( lt_of_le_of_ne hx.1 <| Ne.symm hx0 ) _ );
            · exact ContinuousAt.neg ( ContinuousAt.mul ( continuousAt_const.sub ( continuousAt_id.rpow_const <| Or.inr <| by linarith ) ) <| ContinuousAt.log ( continuousAt_const.sub ( continuousAt_id.rpow_const <| Or.inr <| by linarith ) ) <| by exact ne_of_gt <| sub_pos.mpr <| Real.rpow_lt_one ( by linarith ) ( lt_of_le_of_ne hx.2 hx1 ) <| by linarith );
          · cases lt_or_gt_of_ne hx0 <;> cases lt_or_gt_of_ne hx1 <;> nlinarith [ Real.rpow_pos_of_pos ( lt_of_le_of_ne hx.1 ( Ne.symm hx0 ) ) k, Real.rpow_lt_one hx.1 ( lt_of_le_of_ne hx.2 hx1 ) ( by linarith : 0 < k ), Real.log_le_sub_one_of_pos ( Real.rpow_pos_of_pos ( lt_of_le_of_ne hx.1 ( Ne.symm hx0 ) ) k ), Real.log_le_sub_one_of_pos ( sub_pos.mpr ( Real.rpow_lt_one hx.1 ( lt_of_le_of_ne hx.2 hx1 ) ( by linarith : 0 < k ) ) ) ];
    convert hq_ext_cont using 1;
  -- Since $q_ext$ is continuous on $[0, 1]$ and tends to $1/k$ at endpoints (Lemma 1), it must attain a maximum value $M$ on $[0, 1]$.
  obtain ⟨M, hM⟩ : ∃ M, (∀ x ∈ Set.Icc 0 1, q_ext x ≤ M) ∧ (∃ x ∈ Set.Icc 0 1, q_ext x = M) := by
    exact ⟨ SupSet.sSup ( q_ext '' Set.Icc 0 1 ), fun x hx => le_csSup ( IsCompact.bddAbove ( isCompact_Icc.image_of_continuousOn hq_ext_continuous ) ) ( Set.mem_image_of_mem _ hx ), by simpa using ( IsCompact.sSup_mem ( isCompact_Icc.image_of_continuousOn hq_ext_continuous ) <| Set.Nonempty.image _ <| Set.nonempty_Icc.mpr zero_le_one ) ⟩;
  -- If $M$ is attained at the boundary, then $M = 1/k < \alpha_k$, so $q_ext(x) \le \alpha_k$ for all $x \in [0, 1]$.
  by_cases hM_boundary : M = 1 / k;
  · -- If $M$ is attained at the boundary, then $M = 1/k < \alpha_k$, so $q_ext(x) \le \alpha_k$ for all $x \in [0, 1]$. Hence, $q(x) \le \alpha_k$ for all $x \in (0, 1)$.
    have hq_le_alpha : ∀ x ∈ Set.Ioo 0 1, q k x ≤ alpha k := by
      intros x hx
      have hq_le_M : q k x ≤ M := by
        grind;
      exact hq_le_M.trans ( hM_boundary.symm ▸ by simpa using lemma_l2 k hk |> le_of_lt );
    rcases hx.1.eq_or_lt with h | h
    · subst x; simp [Real.zero_rpow (by positivity : k ≠ 0), Real.zero_rpow (by linarith : k - 1 ≠ 0)]
    rcases hx.2.eq_or_lt with h1 | h1
    · subst x; simp
    exact (div_le_iff₀ (Real.binEntropy_pos (Real.rpow_pos_of_pos h _)
      (Real.rpow_lt_one h.le h1 (by linarith)))).mp (hq_le_alpha x ⟨h,h1⟩)
  · -- If $M$ is attained in $(0, 1)$, then $q'(c) = 0$ for some $c \in (0, 1)$.
    obtain ⟨c, hc⟩ : ∃ c ∈ Set.Ioo 0 1, q_ext c = M ∧ deriv (q k) c = 0 := by
      obtain ⟨c, hc⟩ : ∃ c ∈ Set.Ioo 0 1, q_ext c = M := by
        grind;
      have h_deriv_zero : deriv (q k) c = 0 := by
        have h_max : ∀ x ∈ Set.Ioo 0 1, q k x ≤ q k c := by
          grind
        exact IsLocalMax.deriv_eq_zero ( Filter.eventually_of_mem ( Ioo_mem_nhds hc.1.1 hc.1.2 ) h_max );
      tauto;
    -- By `q_deriv_eq_zero_iff`, $q'(c)=0 \iff BoppanaG(c) = BoppanaG(c^k)$.
    have hBoppanaG_eq : BoppanaG c = BoppanaG (c ^ k) := by
      exact q_deriv_eq_zero_iff k hk c ⟨ hc.1.1, hc.1.2 ⟩ |>.1 hc.2.2;
    -- By `BoppanaG_eq_iff`, this implies $c^k = c$ or $c^k = 1 - c$.
    have hck_eq : c ^ k = c ∨ c ^ k = 1 - c := by
      apply (BoppanaG_eq_iff c (c ^ k) ⟨hc.left.left, hc.left.right⟩ ⟨Real.rpow_pos_of_pos hc.left.left k, Real.rpow_lt_one hc.left.left.le hc.left.right (by linarith)⟩).mp hBoppanaG_eq |> Or.imp (fun h => by
        linarith) (fun h => by
        linarith);
    -- Since $c \in (0, 1)$ and $k > 1$, $c^k < c$, so $c^k \ne c$.
    have hck_ne_c : c ^ k ≠ c := by
      exact ne_of_lt ( by simpa using Real.rpow_lt_rpow_of_exponent_gt hc.1.1 hc.1.2 hk );
    -- Since $c^k = 1 - c$, by `lemma_l5`, this implies $c = 1/(1+\alpha_k)$.
    have hc_eq : c = 1 / (1 + alpha k) := by
      apply lemma_l5 k hk c ⟨hc.left.left, hc.left.right⟩ (hck_eq.resolve_left hck_ne_c);
    -- By `lemma_q_alpha`, $q(c) = \alpha_k$.
    have hq_c : q_ext c = alpha k := by
      convert lemma_q_alpha k hk using 1;
      simp +zetaDelta at *;
      rw [ hc_eq, if_neg ( by rintro ( h | h ) <;> linarith ) ];
    -- Since $M$ is the maximum value of $q_ext$ on $[0, 1]$, we have $q_ext(x) \le M$ for all $x \in [0, 1]$.
    have hq_ext_le_M : ∀ x ∈ Set.Icc 0 1, q_ext x ≤ M := by
      exact hM.1;
    rcases hx.1.eq_or_lt with h | h
    · subst x; simp [Real.zero_rpow (by positivity : k ≠ 0), Real.zero_rpow (by linarith : k - 1 ≠ 0)]
    rcases hx.2.eq_or_lt with h1 | h1
    · subst x; simp
    have hq : q k x ≤ alpha k := by
      have hh := hq_ext_le_M x hx
      rw [← hc.2.1, hq_c] at hh
      simpa [q_ext, h.ne', h1.ne] using hh
    exact (div_le_iff₀ (Real.binEntropy_pos (Real.rpow_pos_of_pos h _)
      (Real.rpow_lt_one h.le h1 (by linarith)))).mp hq

theorem square (x : ℝ) (hx : 0 ≤ x ∧ x ≤ 1) :
    ((1 + Real.sqrt 5) / 2) * x * Real.binEntropy x ≤ Real.binEntropy (x*x) := by
  obtain ⟨ha, hprod⟩ := alpha_spec 2 (by norm_num)
  norm_num at hprod
  have hs := Real.sq_sqrt (by norm_num : (0:ℝ) ≤ 5)
  have haeq : 2 * alpha 2 + 1 = Real.sqrt 5 := by
    apply (mul_self_inj_of_nonneg (by linarith) (Real.sqrt_nonneg 5)).mp
    nlinarith
  have hi := generalized_boppana 2 (by norm_num) x hx
  norm_num [Real.rpow_two, sq] at hi
  have hmul : ((1+Real.sqrt 5)/2) * alpha 2 = 1 := by rw [← haeq]; nlinarith
  calc
    _ = ((1+Real.sqrt 5)/2) * (x * Real.binEntropy x) := by ring
    _ ≤ ((1+Real.sqrt 5)/2) * (alpha 2 * Real.binEntropy (x*x)) :=
      mul_le_mul_of_nonneg_left hi (by positivity)
    _ = _ := by rw [← mul_assoc, hmul, one_mul]

end C6Scalar
end

section
open Real Set
namespace C6Two

private theorem concave_scaled_entropy :
    ConcaveOn ℝ (Iic 0) (fun t : ℝ => binEntropy (exp t) / exp t) := by
  apply concaveOn_of_hasDerivWithinAt2_nonpos (convex_Iic 0)
    (f' := fun t => log (1 - exp t) / exp t)
    (f'' := fun t => -1 / (1 - exp t) - log (1 - exp t) / exp t)
  · exact ((binEntropy_continuous.comp continuous_exp).div continuous_exp
      (fun t => (exp_pos t).ne')).continuousOn
  · intro t ht
    rw [interior_Iic] at ht
    have hp : exp t < 1 := Real.exp_lt_one_iff.mpr ht
    have h := ((hasDerivAt_binEntropy (exp_pos t).ne' hp.ne).comp t (hasDerivAt_exp t)).div
      (hasDerivAt_exp t) (exp_pos t).ne'
    refine (h.congr_deriv ?_).hasDerivWithinAt
    change ((log (1 - exp t) - log (exp t)) * exp t * exp t -
      binEntropy (exp t) * exp t) / (exp t) ^ 2 = _
    simp only [binEntropy, log_inv]
    field_simp [ne_of_gt (exp_pos t)]
    ring
  · intro t ht
    rw [interior_Iic] at ht
    have hp : 0 < 1 - exp t := sub_pos.mpr (Real.exp_lt_one_iff.mpr ht)
    have h := ((((hasDerivAt_const t (1 : ℝ)).sub (hasDerivAt_exp t)).log hp.ne').div
      (hasDerivAt_exp t) (exp_pos t).ne')
    refine (h.congr_deriv ?_).hasDerivWithinAt
    simp only [Pi.sub_apply, zero_sub]
    field_simp [hp.ne', (exp_pos t).ne']
  · intro t ht
    rw [interior_Iic] at ht
    have hp : 0 < 1 - exp t := sub_pos.mpr (Real.exp_lt_one_iff.mpr ht)
    have h := one_sub_inv_le_log_of_pos hp
    field_simp [hp] at h
    field_simp [hp, exp_pos t]
    linarith

theorem pair_bound
    (a : ℝ)
    (diag : ∀ z : ℝ, 0 ≤ z → z ≤ 1 → a * z * binEntropy z ≤ binEntropy (z ^ 2))
    (x y : ℝ) (hx₀ : 0 ≤ x) (hx₁ : x ≤ 1) (hy₀ : 0 ≤ y) (hy₁ : y ≤ 1) :
    a * (x * binEntropy y + y * binEntropy x) ≤ 2 * binEntropy (x * y) := by
  rcases hx₀.eq_or_lt with h | hx
  · simp [← h]
  rcases hy₀.eq_or_lt with h | hy
  · simp [← h]
  have hmx : 2 * log x ∈ Iic (0 : ℝ) := mul_nonpos_of_nonneg_of_nonpos (by norm_num) (log_nonpos hx.le hx₁)
  have hmy : 2 * log y ∈ Iic (0 : ℝ) := mul_nonpos_of_nonneg_of_nonpos (by norm_num) (log_nonpos hy.le hy₁)
  have h := concave_scaled_entropy.2 hmx hmy
    (show (0 : ℝ) ≤ 1 / 2 by norm_num) (show (0 : ℝ) ≤ 1 / 2 by norm_num) (by norm_num)
  dsimp only [smul_eq_mul] at h
  rw [show 1 / 2 * (2 * log x) + 1 / 2 * (2 * log y) = log x + log y by ring,
    exp_add, exp_log hx, exp_log hy,
    show exp (2 * log x) = x ^ 2 by rw [two_mul, exp_add, exp_log hx, sq],
    show exp (2 * log y) = y ^ 2 by rw [two_mul, exp_add, exp_log hy, sq]] at h
  have hx' := mul_le_mul_of_nonneg_left (diag x hx.le hx₁) (sq_nonneg y)
  have hy' := mul_le_mul_of_nonneg_left (diag y hy.le hy₁) (sq_nonneg x)
  field_simp [hx, hy] at h
  apply (mul_le_mul_iff_left₀ (mul_pos hx hy)).mp
  nlinarith only [h, hx', hy']

end C6Two
end

section
open Finset Real
namespace C6Ent

noncomputable section

variable {Ω β : Type*} [Fintype Ω] [Fintype β]

def mass (f : Ω → β) (b : β) : ℝ := by
  classical
  exact ((univ.filter (fun a => f a = b)).card : ℝ) / Fintype.card Ω

def entropy (f : Ω → β) : ℝ := ∑ b, negMulLog (mass f b)

lemma mass_nonneg (f : Ω → β) (b : β) : 0 ≤ mass f b := by
  unfold mass
  positivity

lemma sum_mass [Nonempty Ω] (f : Ω → β) : ∑ b, mass f b = 1 := by
  classical
  have h := Finset.card_eq_sum_card_fiberwise (s := (univ : Finset Ω)) (t := (univ : Finset β)) (f := f) (by simp)
  simp only [mass, ← sum_div, ← Nat.cast_sum, ← h, card_univ]
  exact div_self (by exact_mod_cast Fintype.card_ne_zero)

lemma sum_negMulLog_le_log_card [Nonempty β] (p : β → ℝ) (h0 : ∀ b, 0 ≤ p b)
    (h1 : ∑ b, p b = 1) : ∑ b, negMulLog (p b) ≤ log (Fintype.card β) := by
  let m : ℝ := Fintype.card β
  have hm : m ≠ 0 := by dsimp [m]; exact_mod_cast Fintype.card_ne_zero
  have hJ := Real.concaveOn_negMulLog.le_map_sum (t := (univ : Finset β))
    (w := fun _ => m⁻¹) (p := p) (by intro; intros; positivity)
    (by simp [nsmul_eq_mul, ← show (Fintype.card β : ℝ) = m from rfl, m, Fintype.card_ne_zero])
    (fun b _ => h0 b)
  simp only [smul_eq_mul, ← mul_sum, h1, mul_one, Real.negMulLog, Real.log_inv] at hJ
  have hpos : 0 < m := by dsimp [m]; exact_mod_cast Fintype.card_pos
  change ∑ b, -(p b) * log (p b) ≤ log m
  apply (mul_le_mul_iff_right₀ (inv_pos.mpr hpos)).mp
  simpa using hJ

lemma entropy_le_log_card [Nonempty Ω] [Nonempty β] (f : Ω → β) :
    entropy f ≤ log (Fintype.card β) :=
  sum_negMulLog_le_log_card _ (mass_nonneg f) (sum_mass f)

lemma entropy_id [Nonempty β] : entropy (@id β) = log (Fintype.card β) := by
  classical
  have hc : (Fintype.card β : ℝ) ≠ 0 := by exact_mod_cast Fintype.card_ne_zero
  have heq (x : β) : univ.filter (fun y : β => y = x) = {x} := by ext; simp
  simp [entropy, mass, heq, negMulLog, nsmul_eq_mul, ← mul_assoc, hc]

lemma split_entropy {x y : ℝ} (hx : 0 ≤ x) (hy : 0 ≤ y) :
    negMulLog x + negMulLog y =
      negMulLog (x+y) + (x+y)*binEntropy (x/(x+y)) := by
  by_cases h : x + y = 0
  · have : x = 0 := by linarith
    have : y = 0 := by linarith
    simp [*]
  have hx' : (x+y)*(x/(x+y)) = x := by field_simp
  have hy' : (x+y)*(1-x/(x+y)) = y := by field_simp; ring
  rw [binEntropy_eq_negMulLog_add_negMulLog_one_sub]
  have h1 := negMulLog_mul (x+y) (x/(x+y))
  have h2 := negMulLog_mul (x+y) (1-x/(x+y))
  rw [hx'] at h1
  rw [hy'] at h2
  linarith only [h1,h2]

lemma mass_split (f : Ω → β) (v : Ω → Bool) (b : β) :
    mass (fun w => (f w, v w)) (b,true) +
      mass (fun w => (f w, v w)) (b,false) = mass f b := by
  classical
  let s := univ.filter (fun a : Ω => f a = b)
  have hp : (univ.filter (fun a : Ω => (f a,v a) = (b,true))) = s.filter (fun a => v a = true) := by
    ext; simp [s]
  have hn : (univ.filter (fun a : Ω => (f a,v a) = (b,false))) = s.filter (fun a => ¬v a = true) := by
    ext; simp [s]
  simp only [mass, hp, hn, ← add_div, ← Nat.cast_add, card_filter_add_card_filter_not, s]

lemma entropy_split (f : Ω → β) (v : Ω → Bool) :
    entropy (fun w => (f w, v w)) = entropy f + ∑ b, mass f b *
      binEntropy (mass (fun w => (f w, v w)) (b,true) / mass f b) := by
  classical
  unfold entropy
  rw [Fintype.sum_prod_type, ← sum_add_distrib]
  apply sum_congr rfl
  intro b _
  rw [Fintype.sum_bool, ← mass_split f v b]
  exact split_entropy (mass_nonneg _ _) (mass_nonneg _ _)

lemma entropy_comp_injective {γ : Type*} [Fintype γ] (f : Ω → β) (g : β → γ)
    (hg : Function.Injective g) : entropy (g ∘ f) = entropy f := by
  classical
  unfold entropy
  let s : Finset γ := univ.image g
  have hmass (b : β) : mass (g ∘ f) (g b) = mass f b := by simp [mass, hg.eq_iff]
  calc
    ∑ c, negMulLog (mass (g ∘ f) c) = ∑ c ∈ s, negMulLog (mass (g ∘ f) c) := by
      symm
      apply sum_subset (by simp)
      intro c _ hc
      have hn (a : Ω) : g (f a) ≠ c := fun h => hc (mem_image.mpr ⟨_, mem_univ _, h⟩)
      simp [mass, hn]
    _ = ∑ b, negMulLog (mass f b) := by rw [Finset.sum_image (by exact hg.injOn)]; simp_rw [hmass]

lemma entropy_const [Nonempty Ω] (b : β) : entropy (fun _ : Ω => b) = 0 := by
  classical
  have hc : (Fintype.card Ω : ℝ) ≠ 0 := by exact_mod_cast Fintype.card_ne_zero
  unfold entropy
  apply sum_eq_zero
  intro i _
  by_cases h : b = i <;> simp [mass, h, hc]

end
end C6Ent
end

section
namespace C6Tensor

open Finset Real

private lemma mixture {ι : Type*} (s : Finset ι) (w p : ι → ℝ)
    (hw : ∀ i ∈ s, 0 ≤ w i) (hp : ∀ i ∈ s, p i ∈ Set.Icc 0 1) :
    ∑ i ∈ s, w i * binEntropy (p i) ≤
    (∑ i ∈ s, w i) * binEntropy ((∑ i ∈ s, w i * p i) / ∑ i ∈ s, w i) := by
  let W := ∑ i ∈ s, w i
  have hW : 0 ≤ W := sum_nonneg hw
  rcases hW.eq_or_lt with h|h
  · have hz := (sum_eq_zero_iff_of_nonneg hw).mp h.symm
    change 0 = ∑ i ∈ s, w i at h
    simp [sum_congr rfl (fun i hi => by rw [hz i hi, zero_mul] : ∀ i ∈ s, w i * binEntropy (p i) = 0), ← h]
  · have hh := strictConcave_binEntropy.concaveOn.le_map_sum
        (w := fun i => w i / W) (fun i hi => div_nonneg (hw i hi) h.le)
        (by rw [← sum_div]; exact div_self h.ne') hp
    simp only [smul_eq_mul] at hh
    simp_rw [div_mul_eq_mul_div, ← sum_div] at hh
    exact (div_le_iff₀ h).mp hh |>.trans_eq (mul_comm ..)

private lemma product_growth {ι : Type*} [Fintype ι] (w p : ι → ℝ) (c : ℝ)
    (hw : ∀ i, 0 ≤ w i) (hp : ∀ i, p i ∈ Set.Icc 0 1)
    (two : ∀ x ∈ Set.Icc (0 : ℝ) 1, ∀ y ∈ Set.Icc (0 : ℝ) 1,
      c * (x * binEntropy y + y * binEntropy x) ≤ 2 * binEntropy (x*y)) :
    c * (∑ i, w i * p i) * (∑ i, w i * binEntropy (p i)) ≤
      ∑ a : ι × ι, (w a.1 * w a.2) * binEntropy (p a.1 * p a.2) := by
  have h := sum_le_sum (s := (univ : Finset (ι × ι))) (fun (a : ι × ι) _ =>
    mul_le_mul_of_nonneg_left (two _ (hp a.1) _ (hp a.2)) (mul_nonneg (hw a.1) (hw a.2)))
  have eqn (a b : ι) : w a * w b * (c * (p a * binEntropy (p b) + p b * binEntropy (p a))) =
      c * ((w a * p a) * (w b * binEntropy (p b))) + c * ((w a * binEntropy (p a)) * (w b * p b)) := by ring
  simp only [Fintype.sum_prod_type, eqn, sum_add_distrib, ← mul_sum, ← sum_mul] at h ⊢
  simp_rw [show ∀ a b : ι, w a * w b * (2 * binEntropy (p a * p b)) =
    2 * (w a * w b * binEntropy (p a * p b)) by intros; ring, ← mul_sum] at h
  nlinarith only [h]

end C6Tensor
end

section
namespace C6Tensor
open Finset Real
noncomputable section
variable {Ω β γ : Type*} [Fintype Ω] [Fintype β] [Fintype γ]

def part (s : Finset Ω) (f : Ω → β) (x : β) : ℝ := by
  classical
  exact ((s.filter fun a => f a = x).card : ℝ) / Fintype.card Ω

lemma part_merge [DecidableEq γ] (s : Finset Ω) (f : Ω → β) (u : β → γ) (z : γ) :
    part s (u ∘ f) z = ∑ x ∈ univ.filter (fun x => u x = z), part s f x := by
  classical
  simp only [part, ← sum_div]
  congr 1
  norm_cast
  convert! (sum_card_fiberwise_eq_card_filter s (univ.filter fun x => u x = z) f).symm using 1
  · apply congrArg card
    ext a
    simp

lemma part_pair (s : Finset Ω) (f : Ω → β) (a : β × β) :
    part (s ×ˢ s) (fun q => (f q.1, f q.2)) a = part s f a.1 * part s f a.2 := by
  classical
  have he : (s ×ˢ s).filter (fun q => (f q.1, f q.2) = a) =
      (s.filter fun q => f q = a.1) ×ˢ (s.filter fun q => f q = a.2) := by
    ext q
    simp [Prod.ext_iff, and_assoc, and_left_comm, and_comm]
  simp only [part, he, card_product, Nat.cast_mul, Fintype.card_prod]
  ring

lemma part_mono (s t : Finset Ω) (h : s ⊆ t) (f : Ω → β) (a : β) :
    part s f a ≤ part t f a := by
  classical
  apply div_le_div_of_nonneg_right _ (Nat.cast_nonneg _)
  exact_mod_cast card_le_card (filter_subset_filter _ h)

lemma part_nonneg (s : Finset Ω) (f : Ω → β) (a : β) : 0 ≤ part s f a := by
  unfold part
  positivity

end
end C6Tensor
end

section
namespace C6Tensor
open C6Ent Real Finset
noncomputable section
variable {Ω β : Type*} [Fintype Ω] [Fintype β]

private lemma part_bit (f : Ω → β) (b : Ω → Bool) (x : β) :
    mass (fun a => (f a, b a)) (x,true) = part (univ.filter fun a => b a = true) f x := by
  classical
  simp [mass, part, filter_filter, and_comm]

lemma step (j : Ω × Ω → Ω) (f : Ω → β) (u : β × β → β)
    (hu : ∀ q, f (j q) = u (f q.1, f q.2))
    (b : Ω → Bool) (hb : ∀ q, b (j q) = (b q.1 && b q.2))
    (c k : ℝ) (hk : k ≤ c * mass b true)
    (two : ∀ x ∈ Set.Icc (0 : ℝ) 1, ∀ y ∈ Set.Icc (0 : ℝ) 1,
      c * (x * binEntropy y + y * binEntropy x) ≤ 2 * binEntropy (x*y))
    (ih : k * entropy f ≤ entropy (f ∘ j)) :
    k * entropy (fun a => (f a,b a)) ≤ entropy ((fun a => (f a,b a)) ∘ j) := by
  classical
  let s := univ.filter fun a => b a = true
  let w := mass f
  let p := fun x => part s f x / w x
  have hw : ∀ x, 0 ≤ w x := mass_nonneg _
  have hle (x) : part s f x ≤ w x := part_mono s univ (subset_univ _) f x
  have hp (x) : p x ∈ Set.Icc 0 1 :=
    ⟨div_nonneg (part_nonneg ..) (hw x), div_le_one_of_le₀ (hle x) (hw x)⟩
  have hwp (x) : w x * p x = part s f x := by
    rcases (hw x).eq_or_lt with h|h
    · have hh := part_nonneg s f x
      have := hle x
      rw [← h, zero_mul]
      linarith
    · exact mul_div_cancel₀ _ h.ne'
  have hmean : (∑ x, w x * p x) = mass b true := by
    simp only [hwp, part, mass, ← sum_div]
    congr 1
    norm_cast
    convert! (card_eq_sum_card_fiberwise (s := s) (t := univ) (f := f)
      (fun _ _ => mem_univ _)).symm using 1 <;> first | (apply congrArg card; ext a; simp [s]) | (apply sum_congr rfl; intro x _; apply congrArg card; ext a; simp)
  let W := fun a : β × β => w a.1 * w a.2
  let P := fun a : β × β => p a.1 * p a.2
  let t := fun z => univ.filter fun a => u a = z
  have hmerge (d : Finset Ω) (z : β) :
      part (d ×ˢ d) (f ∘ j) z = ∑ a ∈ t z, part d f a.1 * part d f a.2 := by
    have hh : f ∘ j = u ∘ (fun q : Ω × Ω => (f q.1,f q.2)) := funext hu
    rw [hh, part_merge]
    exact sum_congr rfl (fun i _ => part_pair d f i)
  have hW (z) : mass (f ∘ j) z = ∑ a ∈ t z, W a := by
    simpa [W, w, mass, part] using hmerge univ z
  have hP (z) : mass (fun q => (f (j q), b (j q))) (z,true) = ∑ a ∈ t z, W a * P a := by
    have hs : (univ.filter (fun q => b (j q) = true)) = s ×ˢ s := by
      ext q
      simp [hb, s]
    change mass (fun q => ((f ∘ j) q, (b ∘ j) q)) (z,true) = _
    rw [part_bit (f ∘ j) (b ∘ j), show (univ.filter fun q => (b ∘ j) q = true) = _ from hs, hmerge]
    exact sum_congr rfl fun a _ => by dsimp [W,P]; rw [mul_mul_mul_comm, hwp, hwp]
  have hJ (z) := mixture (t z) W P (fun a _ => mul_nonneg (hw _) (hw _))
      (fun a _ => ⟨mul_nonneg (hp _).1 (hp _).1, mul_le_one₀ (hp _).2 (hp _).1 (hp _).2⟩)
  have hj := sum_le_sum (s := univ) (fun z _ => hJ z)
  simp only [← hW, ← hP] at hj
  rw [show (∑ z, ∑ a ∈ t z, W a * binEntropy (P a)) = ∑ a, W a * binEntropy (P a) from
    sum_fiberwise_of_maps_to (fun _ _ => mem_univ _) _] at hj
  have hg := product_growth w p c hw hp two
  rw [hmean] at hg
  have hnon : 0 ≤ ∑ x, w x * binEntropy (p x) :=
    sum_nonneg (fun x _ => mul_nonneg (hw _) (binEntropy_nonneg (hp _).1 (hp _).2))
  have ht := (mul_le_mul_of_nonneg_right hk hnon).trans (hg.trans hj)
  change k * entropy (fun a => (f a,b a)) ≤ entropy (fun q => ((f ∘ j) q,(b ∘ j) q))
  rw [entropy_split f b, entropy_split (f ∘ j) (b ∘ j), mul_add]
  apply add_le_add ih
  simpa only [part_bit f b, p, w, s, Function.comp_apply] using ht

end
end C6Tensor
end

section
namespace C6Final

open Finset Real C6Ent

private def Bits : ℕ → Type
  | 0 => Unit
  | n+1 => Bits n × Bool

private instance (n : ℕ) : Fintype (Bits n) := by
  induction n with
  | zero => exact inferInstanceAs (Fintype Unit)
  | succ n ih => exact inferInstanceAs (Fintype (Bits n × Bool))

private def encode (s : Finset ℕ) : (n : ℕ) → Bits n
  | 0 => ()
  | n+1 => (encode s n, decide (n ∉ s))

private def both : (n : ℕ) → Bits n × Bits n → Bits n
  | 0, _ => ()
  | n+1, (x,y) => (both n (x.1,y.1), x.2 && y.2)

private lemma encode_union (s t : Finset ℕ) (n : ℕ) :
    encode (s ∪ t) n = both n (encode s n, encode t n) := by
  induction n with
  | zero => rfl
  | succ n ih =>
    by_cases hs : n ∈ s <;> by_cases ht : n ∈ t <;> simp [encode, both, ih, hs, ht] <;> rfl

private lemma encode_agree (s t : Finset ℕ) (n : ℕ) (h : encode s n = encode t n) :
    ∀ i < n, i ∈ s ↔ i ∈ t := by
  induction n with
  | zero => simp
  | succ n ih =>
    intro i hi
    have h' : (encode s n, decide (n ∉ s)) = (encode t n, decide (n ∉ t)) := h
    rcases Prod.mk.inj h' with ⟨h₁,h₂⟩
    rcases Nat.lt_succ_iff_lt_or_eq.mp hi with hlt | rfl
    · exact ih h₁ _ hlt
    · simpa using h₂

private theorem absent_mass (A : Finset (Finset ℕ)) (ha : 0 < A.card) (i : ℕ) :
    mass (fun a : A => decide (i ∉ a.val)) true =
      1 - ((A.filter fun x => i ∈ x).card : ℝ) / A.card := by
  classical
  calc
    mass (fun a : A => decide (i ∉ a.val)) true =
        ((A.filter fun s => i ∉ s).card : ℝ) / A.card := by
      unfold mass
      rw [Fintype.card_coe]
      congr 2
      apply Finset.card_bij (fun a _ => a.val)
      · simp
      · simp
      · intro s hs
        exact ⟨⟨s,(mem_filter.mp hs).1⟩, by simpa using (mem_filter.mp hs).2, rfl⟩
    _ = _ := by
      have hc := card_filter_add_card_filter_not (s := A) (p := fun s => i ∈ s)
      have hc' : ((A.filter fun s => i ∈ s).card : ℝ) + (A.filter fun s => i ∉ s).card = A.card :=
        by exact_mod_cast hc
      field_simp [show (0 : ℝ) < A.card by exact_mod_cast ha]
      linarith

theorem growthImpossible
    (step : ∀ {Ω β : Type} [Fintype Ω] [Fintype β] [Nonempty Ω]
        (j : Ω × Ω → Ω) (f : Ω → β) (u : β × β → β)
        (_hu : ∀ q, f (j q) = u (f q.1, f q.2)) (b : Ω → Bool)
        (_hb : ∀ q, b (j q) = (b q.1 && b q.2)) (k : ℝ),
        k ≤ ((1 + sqrt 5) / 2) * mass b true →
        k * entropy f ≤ entropy (f ∘ j) →
        k * entropy (fun a => (f a,b a)) ≤ entropy ((fun a => (f a,b a)) ∘ j))
    (A : Finset (Finset ℕ)) (hA : 1 < A.card)
    (hclosed : ∀ X ∈ A, ∀ Y ∈ A, X ∪ Y ∈ A) (k : ℝ) (hk : 1 < k)
    (hm : ∀ i : ℕ, k ≤ ((1 + Real.sqrt 5)/2) *
       (1 - ((A.filter fun x => i ∈ x).card : ℝ) / A.card)) : False := by
  classical
  have hc := (Nat.zero_lt_one.trans hA)
  let : Nonempty A := (Finset.card_pos.mp hc).to_subtype
  let j (q : A × A) : A := ⟨q.1.val ∪ q.2.val, hclosed _ q.1.property _ q.2.property⟩
  let f (n : ℕ) (a : A) := encode a.val n
  have bounds (n : ℕ) : k * entropy (f n) ≤ entropy (f n ∘ j) := by
    induction n with
    | zero =>
      change k * entropy (fun _ : A => ()) ≤ entropy (fun _ : A × A => ())
      simp [entropy_const]
    | succ n ih =>
      apply step j (f n) (both n) (fun q => encode_union _ _ _)
        (fun a => decide (n ∉ a.val)) _ k _ ih
      · intro q
        by_cases hs : n ∈ q.1.val <;> by_cases ht : n ∈ q.2.val <;> simp [j, hs, ht]
      · rw [absent_mass _ hc]
        exact hm n
  let N := A.sup (fun s => s.sup id) + 1
  have lim (a : A) (i : ℕ) (hi : i ∈ a.val) : i < N :=
    Nat.lt_succ_of_le ((le_sup (f := id) hi).trans (le_sup (f := fun s : Finset ℕ => s.sup id) a.property))
  have hi : Function.Injective (f N) := by
    intro a b h
    apply Subtype.ext
    ext i
    by_cases hn : i < N
    · exact encode_agree _ _ _ h i hn
    · exact ⟨fun h' => (hn (lim a i h')).elim, fun h' => (hn (lim b i h')).elim⟩
  have H := bounds N
  have he := entropy_comp_injective (@id A) (f N) hi
  change entropy (f N) = entropy (@id A) at he
  rw [he, entropy_id, entropy_comp_injective j _ hi] at H
  have hle := H.trans (entropy_le_log_card j)
  have hp : 0 < log (Fintype.card A : ℝ) := by
    apply Real.log_pos
    rw [Fintype.card_coe]
    exact_mod_cast hA
  nlinarith only [hle, mul_pos (sub_pos.mpr hk) hp]

end C6Final
end

section
namespace C6Sup
open Finset

/-- Pass from uniform entropy growth on a nontrivial closed family to the density bound. -/
theorem lower_bound_of_growth
    (growthImpossible : ∀ A : Finset (Finset ℕ), 1 < A.card →
      (∀ X ∈ A, ∀ Y ∈ A, X ∪ Y ∈ A) → ∀ k : ℝ, 1 < k →
      (∀ i : ℕ, k ≤ ((1 + Real.sqrt 5) / 2) *
        (1 - ((A.filter fun x => i ∈ x).card : ℝ) / A.card)) → False) :
    (3 - Real.sqrt 5) / 2 ≤ Constant6a.C6a := by
  classical
  unfold Constant6a.C6a
  apply le_csSup
  · refine ⟨1, ?_⟩
    intro c hc
    let S : Finset (Finset ℕ) := {{0}}
    obtain ⟨i, hi⟩ := hc S (by decide) (by decide)
    have hcard : (S.filter (fun x => i ∈ x)).card ≤ S.card := card_filter_le ..
    have h := hi.trans (Nat.cast_le.mpr hcard)
    simpa [S] using h
  · intro A hne hclosed
    have hs := Real.sq_sqrt (by norm_num : 0 ≤ (5 : ℝ))
    have hsq := Real.sqrt_nonneg (5 : ℝ)
    have hgt : 1 < Real.sqrt 5 := by nlinarith
    by_cases h0 : A.card = 0
    · exact ⟨0, by simp [card_eq_zero.mp h0]⟩
    by_cases h1 : A.card = 1
    · obtain ⟨x, rfl⟩ := card_eq_one.mp h1
      have hx : x.Nonempty := nonempty_iff_ne_empty.mpr (fun h => hne (by rw [h]))
      obtain ⟨i, hi⟩ := hx
      refine ⟨i, ?_⟩
      simp [Finset.filter_singleton, hi]
      linarith
    have hA : 1 < A.card := by omega
    have hc : 0 < (A.card : ℝ) := by exact_mod_cast (by omega : 0 < A.card)
    let freq (i : ℕ) := (A.filter fun x => i ∈ x).card
    let P (n : ℕ) := ∃ i, freq i = n
    have hf (i : ℕ) : freq i ≤ A.card := card_filter_le ..
    obtain ⟨j, hj⟩ := (Nat.findGreatest_spec (P := P) (hf 0) (show P (freq 0) from ⟨0,rfl⟩) :
      P (Nat.findGreatest P A.card))
    have hmax (i : ℕ) : freq i ≤ freq j := by
      rw [hj]
      exact Nat.le_findGreatest (hf i) (show P (freq i) from ⟨i,rfl⟩)
    refine ⟨j, ?_⟩
    by_contra! h
    change (freq j : ℝ) < (3 - Real.sqrt 5) / 2 * A.card at h
    let φ := (1 + Real.sqrt 5) / 2
    have hφ : 0 < φ := by dsimp [φ]; linarith
    let k := φ * (1 - (freq j : ℝ) / A.card)
    apply growthImpossible A hA hclosed k
    · have hd := (div_lt_iff₀ hc).mpr h
      change 1 < φ * (1 - (freq j : ℝ) / A.card)
      calc
        1 = φ * (1 - (3 - Real.sqrt 5) / 2) := by dsimp [φ]; nlinarith
        _ < _ := mul_lt_mul_of_pos_left (sub_lt_sub_left hd 1) hφ
    · intro i
      change φ * (1 - (freq j : ℝ) / A.card) ≤ φ * (1 - (freq i : ℝ) / A.card)
      gcongr
      exact hmax i

end C6Sup
end

theorem OMA.solution : type_of% @Constant6a.c6a_lower_bound_first := by
  apply C6Sup.lower_bound_of_growth
  apply C6Final.growthImpossible
  intro Ω β _ _ _ j f u hu b hb k hk ih
  apply C6Tensor.step j f u hu b hb ((1 + Real.sqrt 5) / 2) k hk _ ih
  intro x hx y hy
  apply C6Two.pair_bound _ _ x y hx.1 hx.2 hy.1 hy.2
  intro z hz₀ hz₁
  simpa only [sq] using C6Scalar.square z ⟨hz₀,hz₁⟩
