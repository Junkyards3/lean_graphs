import tactic 
import data.nat.parity
import data.multiset.basic 


open finset
open function
open list

namespace aux_walk

def rmv_unt_aux {A : Type} [decidable_eq A] : A → list A → list A 
  | a [] := []
  | a (x::xs) := ite (a ∈ (x::xs)) (rmv_unt_aux a xs) (x::xs)
  
lemma rmv_aux_not_a {A : Type} [decidable_eq A] : ∀ a : A, ∀ l : list A,
a ∉ rmv_unt_aux a l :=
begin 
  intros a l,
  induction l with x xs hxs,
  unfold rmv_unt_aux,
  exact not_mem_nil a,
  unfold rmv_unt_aux,
  split_ifs,
  exact hxs,
  exact h,
end

lemma rmv_aux_inf_count {A : Type} [decidable_eq A] : ∀ a b: A, ∀ l : list A,
count b (rmv_unt_aux a l) ≤ count b l :=
begin 
  intros a b l,
  induction l with x xs hxs,
  unfold rmv_unt_aux,
  unfold rmv_unt_aux,
  split_ifs,
  transitivity (count b xs),
  exact hxs,
  exact count_le_count_cons b x xs,
  refl,
end

lemma rmv_aux_smaller {A : Type} [decidable_eq A] : ∀ a: A, ∀ l : list A,
length (rmv_unt_aux a l) ≤ length l :=
begin 
  intros a l,
  induction l with x xs hxs,
  unfold rmv_unt_aux,
  unfold rmv_unt_aux,
  split_ifs,
  transitivity (xs.length),
  exact hxs,
  rw length_cons,
  linarith,
  refl,
end

lemma rmv_aux_in {A : Type} [decidable_eq A] : ∀ a b: A, ∀ l : list A,
b ∈ (rmv_unt_aux a l) → b ∈ l :=
begin 
  intros a b l,
  induction l with x xs hxs,
  {
    unfold rmv_unt_aux,
    intro hb, exact hb,
  },
  {
    intro hb,
    unfold rmv_unt_aux at hb,
    split_ifs at hb,
    specialize hxs hb,
    exact mem_cons_of_mem x hxs,
    exact hb,
  }
end

lemma rmv_aux_suffix {A : Type} [decidable_eq A] : ∀ a : A, ∀ l : list A,
(rmv_unt_aux a l) = l ∨ (a ::(rmv_unt_aux a l)) <:+ l :=
begin 
  intros a l,
  induction l with x xs hxs,
  {
    left,
    unfold rmv_unt_aux,
  },
  {
    repeat {unfold rmv_unt_aux},
    split_ifs, swap,
    {
      left,
      split;refl,
    },
    {
      right,
      rw suffix_cons_iff,
      cases hxs with hxs hxs,
      {
        repeat {rw hxs},
        left,
        congr,
        rw mem_cons_iff at h,
        cases h with h h, exact h,
        induction xs with y ys hys,
        {
          exfalso,
          exact not_mem_nil a h,
        },
        {
          unfold rmv_unt_aux at hxs,
          split_ifs at hxs,
          exfalso,
          apply_fun list.length at hxs,
          simp at hxs,
          have hxs' := rmv_aux_smaller a ys,
          linarith,
        }
      },
      {
        right,
        exact hxs,
      }
    }

  }
end

lemma rmv_aux_eq {A : Type} [decidable_eq A] : ∀ a : A, ∀ l : list A,
(rmv_unt_aux a l) = l ↔ (a ∉ l) :=
begin
  intros a l,
  have hal := rmv_aux_suffix a l,
  cases hal with hal hal, swap,
  {
    split,
    intro h,
    exfalso,
    rw h at hal,
    replace hal := length_le_of_sublist (sublist_of_suffix hal),
    rw length_cons at hal,
    linarith,
    intro h,
    exfalso,
    apply h,
    replace hal := sublist_of_suffix hal,
    replace hal := sublist.subset hal,
    apply hal,
    exact mem_cons_self a (rmv_unt_aux a l),
  },
  {
    rw hal,
    simp,
    induction l with x xs hxs,
    exact not_mem_nil a,
    unfold rmv_unt_aux at hal,
    split_ifs at hal, swap, exact h,
    exfalso,
    apply_fun list.length at hal,
    have hal' := rmv_aux_smaller a xs,
    rw length_cons at hal,
    linarith,
  }
  
end

lemma rmv_aux_empty {A : Type} [decidable_eq A] [inhabited A] : ∀ a : A, ∀ l : list A,
(rmv_unt_aux a l) = nil ↔ l = nil ∨ l.ilast = a :=
begin 
  intros a l,
  split,
  {
    intro h,
    induction l with x xs hxs,
    {
      left,
      refl,
    },
    {
      right,
      unfold rmv_unt_aux at h,
      split_ifs at h,
      {
        specialize hxs h,
        cases hxs with hxs hxs,
        rw hxs at *,
        finish,
      },
      {
        
      }
    }
  }
end
def rmv_unt {A : Type} [decidable_eq A] : list A → list A 
  | [] := []
  | (x::xs) := have (rmv_unt_aux x xs).sizeof < 1 + xs.sizeof :=
  begin 
    induction xs with y ys hys,
    {
      unfold rmv_unt_aux,
      linarith,
    },
    {
      unfold rmv_unt_aux,
      split_ifs,
      {
        unfold list.sizeof,
        linarith,
      },
      {
        linarith,
      }
    }
  end,
  x::rmv_unt(rmv_unt_aux x xs)
    
lemma rmv_in {A : Type} [decidable_eq A] : ∀ b: A, ∀ l : list A,
 b ∈ (rmv_unt l) → b ∈ l  :=
begin 
  intros b l,
  obtain ⟨n, hn⟩ : {n : ℕ // l.length = n} := ⟨_, rfl⟩,
  revert l,
  apply nat.strong_induction_on n,
  intros m hm l hl hb,
  induction l with x xs hxs,
  {
    unfold rmv_unt at hb,
    exact hb,
  },
  {
    unfold rmv_unt at hb,
    rw mem_cons_iff at hb ⊢,
    simp at hl,
    cases hb with hb hb,
    {
      left,
      exact hb,
    },
    {
      right,
      apply rmv_aux_in x,
      apply hm (rmv_unt_aux x xs).length,
      rw ← hl,
      have hl' := rmv_aux_smaller x xs,
      linarith,
      refl,
      exact hb,
    }
  }
end

lemma rmv_nodup {A : Type} [decidable_eq A] : ∀ l : list A,
nodup (rmv_unt l) :=
begin 
  intros l,
  obtain ⟨n, hn⟩ : {n : ℕ // l.length = n} := ⟨_, rfl⟩,
  revert l,
  apply nat.strong_induction_on n,
  intros m hm l hl,
  induction l with x xs hxs,
  {
    unfold rmv_unt,
    exact nodup_nil,
  },
  {
    unfold rmv_unt,
    clear hxs,
    rw nodup_cons,
    split,
    {
      intro hx,
      apply rmv_aux_not_a x xs,
      apply rmv_in,
      exact hx,
    },
    {
      apply hm, swap 3,
      exact (rmv_unt_aux x xs).length,
      rw ← hl,
      rw length_cons,
      have hxs := rmv_aux_smaller x xs,
      linarith,
      refl,
    }
  }
end

lemma rmv_empty {A : Type} [decidable_eq A] : ∀ l : list A,
l = nil ↔ rmv_unt l = nil := 
begin 
  intro l,
  split,
  {
    intro h,
    rw h,
    unfold rmv_unt,
  },
  {
    intro h,
    induction l with x xs hxs,
    refl,
    exfalso,
    unfold rmv_unt at h,
    contradiction,
  }
end

lemma rmv_head {A : Type} [decidable_eq A] [inhabited A] : ∀ l : list A,
(l ≠ nil) → (l.head = list.head (rmv_unt l)) :=
begin 
  intros l hl,
  induction l with x xs hxs,
  tauto,
  unfold rmv_unt,
  simp,
end

lemma rmv_last {A : Type} [decidable_eq A] [inhabited A] : ∀ l : list A,
(l ≠ nil) → (l.ilast = list.ilast (rmv_unt l)) :=
begin 
  intros l hl,
  induction l with x xs hxs,
  tauto,
  unfold rmv_unt,
  by_cases hs : xs = nil,
  {
    rw hs,
    unfold rmv_unt_aux rmv_unt,
  },
  {
    specialize hxs hs,
    repeat {rw ilast_eq_last'},
    have h1 := last'_append_of_ne_nil [x] hs,
  }
end
end aux_walk