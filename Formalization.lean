import Mathlib.LinearAlgebra.Eigenspace.Basic
import Mathlib.LinearAlgebra.Eigenspace.Minpoly
import Mathlib.LinearAlgebra.Eigenspace.Semisimple
import Mathlib.LinearAlgebra.FiniteDimensional.Lemmas
import Mathlib.LinearAlgebra.Charpoly.Basic
import Mathlib.RingTheory.Nilpotent.Basic
import Mathlib.RingTheory.Finiteness.Nilpotent
import Mathlib.RingTheory.Ideal.Quotient.Operations
import Mathlib.RingTheory.Coprime.Ideal
import Mathlib.RingTheory.Polynomial.Ideal
import Mathlib.Algebra.Polynomial.AlgebraMap
import Mathlib.Algebra.Polynomial.Module.AEval
import Mathlib.RingTheory.Adjoin.Polynomial.Basic
import Mathlib.Algebra.DirectSum.Module
import Mathlib.Algebra.DirectSum.Decomposition

namespace AI4MATH

open Polynomial

noncomputable section

private lemma maxGenEigenspace_eq_bot_of_not_hasEigenvalue
    {K V : Type*} [Field K] [AddCommGroup V] [Module K V] [FiniteDimensional K V]
    (T : Module.End K V) {μ : K} (hμ : ¬ T.HasEigenvalue μ) :
    T.maxGenEigenspace μ = ⊥ := by
  rw [T.maxGenEigenspace_eq_genEigenspace_finrank]
  by_cases hd : Module.finrank K V = 0
  · rw [hd]
    exact
      (Module.End.genEigenspace_zero (f := T) :
        (T.genEigenspace μ) (0 : ℕ∞) = (⊥ : Submodule K V))
  · by_contra hne
    exact hμ ((Module.End.hasGenEigenvalue_iff_hasEigenvalue (f := T)
      (k := Module.finrank K V) (Nat.pos_of_ne_zero hd)).mp hne)

private lemma aeval_sub_C_apply_eq_zero_of_mem_maxGen
    {K V : Type*} [Field K] [AddCommGroup V] [Module K V] [FiniteDimensional K V]
    (T : Module.End K V) {μ : K} {p : Polynomial K}
    (hp : p - Polynomial.C μ ∈
      Ideal.span ({(Polynomial.X - Polynomial.C μ) ^ Module.finrank K V} : Set (Polynomial K)))
    {m : V} (hm : m ∈ T.maxGenEigenspace μ) :
    ((Polynomial.aeval T) (p - Polynomial.C μ)) m = 0 := by
  have hdiv := Ideal.mem_span_singleton.mp hp
  rcases hdiv with ⟨q, hq⟩
  rw [mul_comm] at hq
  have hmg : m ∈ T.genEigenspace μ (Module.finrank K V) := by
    simpa [T.maxGenEigenspace_eq_genEigenspace_finrank μ] using hm
  have hm' :
      m ∈ LinearMap.ker ((T - algebraMap K (Module.End K V) μ) ^ Module.finrank K V) := by
    simpa [Module.End.genEigenspace_nat, Algebra.algebraMap_eq_smul_one] using hmg
  have hpow :
      Polynomial.aeval T ((Polynomial.X - Polynomial.C μ) ^ Module.finrank K V) =
        (T - algebraMap K (Module.End K V) μ) ^ Module.finrank K V := by
    simp
  rw [hq, map_mul, Module.End.mul_apply, hpow]
  simpa using congrArg ((Polynomial.aeval T) q) (LinearMap.mem_ker.mp hm')

theorem jordan_chevalley_decomposition
    {K V : Type*} [Field K] [IsAlgClosed K] [AddCommGroup V] [Module K V]
    [FiniteDimensional K V] (T : Module.End K V) :
    ∃ S N : Module.End K V,
      T = S + N ∧
      S.IsSemisimple ∧
      IsNilpotent N ∧
      Commute S N ∧
      S ∈ Algebra.adjoin K ({T} : Set (Module.End K V)) ∧
      N ∈ Algebra.adjoin K ({T} : Set (Module.End K V)) ∧
      ∀ S' N' : Module.End K V,
        T = S' + N' →
        S'.IsSemisimple →
        IsNilpotent N' →
        Commute S' N' →
        S' = S ∧ N' = N := by
  classical
  let d : ℕ := Module.finrank K V
  let I : T.Eigenvalues → Ideal (Polynomial K) :=
    fun μ => Ideal.span ({(Polynomial.X - Polynomial.C (μ : K)) ^ d} : Set (Polynomial K))
  have hbase :
      Pairwise (Function.onFun IsCoprime
        (fun μ : T.Eigenvalues => Polynomial.X - Polynomial.C (μ : K))) :=
    Polynomial.pairwise_coprime_X_sub_C (s := fun μ : T.Eigenvalues => (μ : K))
      Subtype.val_injective
  have hI : Pairwise (Function.onFun IsCoprime I) := by
    intro μ ν hμν
    exact (Ideal.isCoprime_span_singleton_iff
      ((Polynomial.X - Polynomial.C (μ : K)) ^ d)
      ((Polynomial.X - Polynomial.C (ν : K)) ^ d)).2 ((hbase hμν).pow)
  obtain ⟨p, hp⟩ := Ideal.exists_forall_sub_mem_ideal hI
    (fun μ : T.Eigenvalues => Polynomial.C (μ : K))
  let S : Module.End K V := Polynomial.aeval T p
  let N : Module.End K V := T - S
  have hS_apply_of_hasEigenvalue :
      ∀ {μ : K}, T.HasEigenvalue μ → ∀ {m : V}, m ∈ T.maxGenEigenspace μ → S m = μ • m := by
    intro μ hμ m hm
    have hzero : ((Polynomial.aeval T) (p - Polynomial.C μ)) m = 0 := by
      simpa [I, d] using
        (aeval_sub_C_apply_eq_zero_of_mem_maxGen T (p := p) (μ := μ) (hp ⟨μ, hμ⟩) hm)
    simpa [S, Polynomial.aeval_sub, Polynomial.aeval_C, Algebra.algebraMap_eq_smul_one,
      sub_eq_zero] using hzero
  have hS_apply_of_mem_max :
      ∀ {μ : K} {m : V}, m ∈ T.maxGenEigenspace μ → S m = μ • m := by
    intro μ m hm
    by_cases hμ : T.HasEigenvalue μ
    · exact hS_apply_of_hasEigenvalue hμ hm
    · have hm0 : m = 0 := by
        simpa [maxGenEigenspace_eq_bot_of_not_hasEigenvalue T hμ] using hm
      simp [hm0]
  have hN_apply_of_mem_max :
      ∀ {μ : K} {m : V}, m ∈ T.maxGenEigenspace μ →
        N m = ((T - algebraMap K (Module.End K V) μ) m) := by
    intro μ m hm
    simp [N, hS_apply_of_mem_max hm, Algebra.algebraMap_eq_smul_one]
  have hS_mem : S ∈ Algebra.adjoin K ({T} : Set (Module.End K V)) := by
    change Polynomial.aeval T p ∈ Algebra.adjoin K ({T} : Set (Module.End K V))
    exact Polynomial.aeval_mem_adjoin_singleton K T (p := p)
  have hN_mem : N ∈ Algebra.adjoin K ({T} : Set (Module.End K V)) := by
    simpa [N] using
      (Algebra.adjoin K ({T} : Set (Module.End K V))).sub_mem
        (Algebra.self_mem_adjoin_singleton K T) hS_mem
  have hcomm : Commute S N := by
    have hTN : Commute T N := Algebra.commute_of_mem_adjoin_self hN_mem
    exact (Algebra.commute_of_mem_adjoin_singleton_of_commute hS_mem hTN.symm).symm
  have hN_nil : IsNilpotent N := by
    rw [Module.End.isNilpotent_iff_of_finite]
    intro m
    use d
    have htop_le : (⊤ : Submodule K V) ≤ LinearMap.ker (N ^ d) := by
      rw [← Module.End.iSup_maxGenEigenspace_eq_top T]
      refine iSup_le fun μ => ?_
      intro x hx
      let A : Module.End K V := T - algebraMap K (Module.End K V) μ
      have hA_maps : Set.MapsTo A (T.maxGenEigenspace μ) (T.maxGenEigenspace μ) := by
        simpa [A] using
          (Module.End.mapsTo_maxGenEigenspace_of_comm
            (f := T) (g := T - algebraMap K (Module.End K V) μ)
            (Algebra.mul_sub_algebraMap_commutes T μ) μ)
      have hN_maps : Set.MapsTo N (T.maxGenEigenspace μ) (T.maxGenEigenspace μ) := by
        intro y hy
        rw [hN_apply_of_mem_max hy]
        exact hA_maps hy
      have hpow_eq :
          ∀ n : ℕ, ∀ {y : V}, y ∈ T.maxGenEigenspace μ →
            (N ^ n) y = (A ^ n) y ∧ (N ^ n) y ∈ T.maxGenEigenspace μ := by
        intro n
        induction n with
        | zero =>
            intro y hy
            simp [hy]
        | succ n ih =>
            intro y hy
            rcases ih hy with ⟨hpow, hmem⟩
            constructor
            · rw [pow_succ', pow_succ', Module.End.mul_apply, Module.End.mul_apply,
                hN_apply_of_mem_max hmem, hpow]
            · rw [pow_succ', Module.End.mul_apply]
              exact hN_maps hmem
      have hxg : x ∈ T.genEigenspace μ d := by
        simpa [d, T.maxGenEigenspace_eq_genEigenspace_finrank μ] using hx
      have hA_zero : (A ^ d) x = 0 := by
        simpa [A, Module.End.genEigenspace_nat, Algebra.algebraMap_eq_smul_one] using hxg
      rw [LinearMap.mem_ker]
      exact (hpow_eq d hx).1.trans hA_zero
    exact LinearMap.mem_ker.mp (htop_le trivial)
  let q : Polynomial K :=
    (Finset.univ : Finset T.Eigenvalues).prod
      (fun μ => Polynomial.X - Polynomial.C (μ : K))
  have hq_squarefree : Squarefree q := by
    dsimp [q]
    refine Finset.squarefree_prod_of_pairwise_isCoprime (s := Finset.univ)
      (f := fun μ : T.Eigenvalues => Polynomial.X - Polynomial.C (μ : K)) ?_ ?_
    · intro μ _ ν _ hμν
      exact (hbase hμν).isRelPrime
    · intro μ _
      exact (Polynomial.irreducible_X_sub_C (μ : K)).squarefree
  have hS_ann : Polynomial.aeval S q = 0 := by
    apply LinearMap.ext
    intro m
    have htop_le : (⊤ : Submodule K V) ≤ LinearMap.ker (Polynomial.aeval S q) := by
      rw [← Module.End.iSup_maxGenEigenspace_eq_top T]
      refine iSup_le fun μ => ?_
      intro x hx
      rw [LinearMap.mem_ker]
      by_cases hμ : T.HasEigenvalue μ
      · have hxS : S x = μ • x := hS_apply_of_hasEigenvalue hμ hx
        have hqeval : q.eval μ = 0 := by
          rw [show q = (Finset.univ : Finset T.Eigenvalues).prod
              (fun ν => Polynomial.X - Polynomial.C (ν : K)) from rfl]
          rw [Polynomial.eval_prod]
          exact Finset.prod_eq_zero (s := Finset.univ) (i := Subtype.mk μ hμ)
            (Finset.mem_univ _) (by simp)
        rw [Module.End.aeval_apply_of_mem_apply_eq_smul hxS, hqeval, zero_smul]
      · have hx0 : x = 0 := by
          simpa [maxGenEigenspace_eq_bot_of_not_hasEigenvalue T hμ] using hx
        simp [hx0]
    simpa using LinearMap.mem_ker.mp (htop_le trivial)
  have hS_ss : S.IsSemisimple :=
    Module.End.isSemisimple_of_squarefree_aeval_eq_zero hq_squarefree hS_ann
  have hT_decomp : T = S + N := by
    change T = S + (T - S)
    abel
  refine ⟨S, N, hT_decomp, hS_ss, hN_nil, hcomm, hS_mem, hN_mem, ?_⟩
  intro S' N' hT' hS' hN' hSN'
  have hTS' : Commute T S' := by
    rw [hT']
    exact (Commute.refl S').add_left hSN'.symm
  have hdiff' : T - S' = N' := by
    rw [hT']
    abel
  have hnil_diff' : IsNilpotent (T - S') := by
    simpa [hdiff'] using hN'
  have hS'_apply_of_mem_max :
      ∀ {μ : K} {m : V}, m ∈ T.maxGenEigenspace μ → S' m = μ • m := by
    intro μ m hm
    exact Module.End.apply_eq_of_mem_of_comm_of_isFinitelySemisimple_of_isNil
      (f := T) (g := S') hm hTS'
      ((Module.End.isFinitelySemisimple_iff_isSemisimple (f := S')).2 hS') hnil_diff'
  have hS'_eq : S' = S := by
    apply LinearMap.ext
    intro m
    have htop_le : (⊤ : Submodule K V) ≤ LinearMap.ker (S' - S) := by
      rw [← Module.End.iSup_maxGenEigenspace_eq_top T]
      refine iSup_le fun μ => ?_
      intro x hx
      rw [LinearMap.mem_ker, LinearMap.sub_apply,
        hS'_apply_of_mem_max hx, hS_apply_of_mem_max hx, sub_self]
    exact sub_eq_zero.mp (LinearMap.mem_ker.mp (htop_le trivial))
  have hN'_eq : N' = N := by
    calc
      N' = T - S' := by
        rw [hT']
        abel
      _ = T - S := by rw [hS'_eq]
      _ = N := by rfl
  exact ⟨hS'_eq, hN'_eq⟩

end

end AI4MATH
