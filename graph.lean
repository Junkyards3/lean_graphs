import tactic 
import data.nat.parity
import data.sym.sym2
import data.multiset.basic 
import algebra.big_operators.basic 
import aux_walk 

open finset
open function
open sym2
open list
open aux_walk

open_locale big_operators

structure graph :=
(V : Type)
(E : Type)
(edge : E → (sym2 V))

structure finite_graph extends graph :=
(dec_V : decidable_eq V)
(dec_E : decidable_eq E)
(fin_V : fintype V)
(fin_E : fintype E)

section graph

variables {G : graph}


def graph.simple (G : graph) : Prop :=
  injective G.edge ∧ ∀ e : G.E, ¬ is_diag (G.edge e)

def graph.simple_graph_from_edgeset {W : Type} (S : set (sym2 W)) : graph :=
{
  V := W,
  E := S,
  edge := λe,↑e
}


def graph.incid (G : graph) (v w : G.V) : Prop := ∃ e : G.E, G.edge e = ⟦(v,w)⟧

theorem graph.exists_unique_edge_simple_graph (G : graph) {h : G.simple} {v w : G.V} :
G.incid v w → ∃! (e:G.E), G.edge e = ⟦(v,w)⟧ :=
begin 
  intro hvw,
  unfold exists_unique,
  cases hvw with e he,
  use e,
  split,
  exact he,
  intros e' he',
  apply h.1,
  exact (rfl.congr (eq.symm he)).mp he',
end

def graph.isolated_vertex (G : graph) (v : G.V) : Prop := ∀ e : G.E, v ∉ G.edge e

theorem graph.isolated_def (G : graph) (v : G.V) : G.isolated_vertex v ↔ ∀ e : G.E, v ∉ G.edge e := by refl

section finite_graph

variable {F : finite_graph}

instance : fintype F.V := begin 
  exact F.fin_V,
end
instance : fintype F.E := begin 
  exact F.fin_E,
end
instance : decidable_eq F.V := begin 
  exact F.dec_V,
end
instance : decidable_eq F.E := begin 
  exact F.dec_E,
end

instance finite_graph.get_graph : has_coe (finite_graph) (graph) := begin 
  fconstructor,
  exact finite_graph.to_graph,
end

def finite_graph.simple (F : finite_graph) : Prop := F.to_graph.simple

instance {V : Type} [fintype V] [decidable_eq V] : fintype (sym2 V) := 
begin 
  exact quotient.fintype (sym2.rel.setoid V),
end 

def finite_graph.degree (F : finite_graph) (v : F.V) : ℕ := 
card (filter (λe:F.E,v ∈ F.edge e) univ) + card (filter (λe:F.E,F.edge e = ⟦(v,v)⟧) univ)

lemma finite_graph.degree_def (F : finite_graph) : ∀ v : F.V,
F.degree v = card (filter (λe:F.E,v ∈ F.edge e) univ) + 
card (filter (λe:F.E,F.edge e = ⟦(v,v)⟧) univ) := by finish

lemma finite_graph.degree_separate (F : finite_graph) : (λv,F.degree v) =  λv:F.V,
card (filter (λe:F.E,v ∈ F.edge e ∧ F.edge e ≠ ⟦(v,v)⟧) univ) + 
2*card (filter (λe:F.E,F.edge e = ⟦(v,v)⟧) univ) :=
begin 
  funext,
  rw two_mul,
  rw F.degree_def v,
  simp, rw ← add_assoc,
  congr' 1,
  rw ← card_disjoint_union,swap,
  {
    rw disjoint_filter,
    simp,
  },
  {
    rw ← filter_or,
    congr,
    funext,
    simp,
    split,
    intros hv,
    finish,
    intros hv,
    finish,
  }
end

instance : decidable_pred (odd ∘ F.degree) :=
begin 
  intro v,
  apply nat.decidable_pred_odd,
end

theorem finite_graph.even_sum_of_degrees (F : finite_graph) : even (∑ v : F.V, F.degree v) :=
begin 
  rw F.degree_separate,
  norm_num,
  rw sum_add_distrib,
  apply nat.even.add_even,swap,
  {
    apply finset.sum_induction,
    intros a b ha hb, exact nat.even.add_even ha hb, exact nat.even_zero,
    simp, intros v, rw even_iff_two_dvd, simp,
  },
  {
    have hn : ∑ (x : F.V), (filter (λ (e : F.E), x ∈ F.edge e ∧ ¬F.edge e = ⟦(x, x)⟧) univ).card = 
    (∑ (x : F.V), ∑ (e : F.E), ite (x ∈ F.edge e ∧ ¬F.edge e = ⟦(x,x)⟧) 1 0),
    {
      congr,
      funext v,
      finish,
    },
    rw hn,
    rw sum_comm,
    apply finset.sum_induction,
    intros a b ha hb, exact nat.even.add_even ha hb, exact nat.even_zero,
    intros e he, clear he,
    have he_rep := quotient.exists_rep (F.edge e),
    rcases he_rep with ⟨⟨v,w⟩,hvw⟩,
    rw ← hvw,
    simp [-quotient.eq],
    have hf : filter (λ (x : F.V), (x = v ∨ x = w) ∧ ¬⟦(v, w)⟧ = ⟦(x, x)⟧) univ = ite (v = w) ∅ {v,w},
    {
      ext u,
      simp [-quotient.eq],
      split,
      rintros ⟨h1|h1,h2⟩,
      rw h1 at h2 ⊢,
      split_ifs,exfalso,rw ← h at h2, contradiction,
      simp [-quotient.eq],
      split_ifs,
      exfalso,
      rw [h,h1] at h2, contradiction, 
      rw h1, simp [-quotient.eq],
      intro hu, split_ifs at hu,
      exfalso, finish,
      simp [-quotient.eq] at hu,
      split;
      cases hu with huv huw,
      left, assumption,
      right, assumption,
      rw huv, intro hs, apply h,
      rw eq_iff at hs,
      simp at hs, symmetry, assumption,
      rw eq_iff,
      simp,
      intro hvu, finish,
    },
    rw hf,
    split_ifs,
    simp,
    rw card_insert_of_not_mem,
    rw finset.card_singleton, ring_nf, exact even_bit0 1,
    simp, exact h,
  }
end

lemma finite_graph.parity_sum_of_odd_terms {S : Type} [decidable_eq S] {A : finset S} (f : S → ℕ) :
 (∀ a ∈ A, odd (f a)) → 
(even (∑ a in A, f a) ↔ even A.card) :=
begin 
  apply finset.induction_on A,
  {
    intros he,
    split,
    intros he',
    simp,
    intros he',
    simp,
  },
  {
    intros a S haS hS hA,
    have hS' : even (∑ a in S, f a) ↔ even S.card,
    {
      apply hS,
      intros a ha,
      apply hA,
      finish,
    },
    rw card_insert_of_not_mem haS,
    rw sum_insert haS,
    repeat {rw nat.even_add'},
    specialize hA a (by simp),
    simp [hA],
    rwa hS',
  }
  
end


theorem finite_graph.even_number_of_odd_degrees (F : finite_graph) : even (card (filter (odd ∘ F.degree) univ)) :=
begin 
  have h : even (∑ v in filter (odd ∘ F.degree) univ, F.degree v),
  {
    have heo := sum_filter_add_sum_filter_not univ (odd ∘ F.degree) F.degree,
    have hcc := F.even_sum_of_degrees,
    rw ← heo at hcc,
    rw nat.even_add at hcc,
    rw hcc,
    apply finset.sum_induction,
    intros a b, exact nat.even.add_even,
    exact nat.even_zero,
    intros v hv,
    finish,
  },
  rw  finite_graph.parity_sum_of_odd_terms at h,
  exact h,
  simp,
end

def finite_graph.isolated_vertex (F : finite_graph) (v : F.V) : Prop := ∀ e : F.E, v ∉ F.edge e

theorem finite_graph.isolated_def (F : finite_graph) (v : F.V) : 
F.isolated_vertex v ↔ ∀ e : F.E, v ∉ F.edge e := by refl

theorem finite_graph.isolated_degree_zero (F : finite_graph) (v : F.V) : 
F.isolated_vertex v ↔ F.degree v = 0 :=
begin 
  rw F.isolated_def,
  split,
  {
    intro h,
    rw F.degree_def,
    norm_num,
    split,
    apply filter_false_of_mem,
    simp, exact h,
    apply filter_false_of_mem,
    simp, intros e hne, specialize h e, finish,
  },
  {
    intros hv e hn,
    rw F.degree_def at hv, norm_num at hv,
    cases hv with hv1 hv2,
    rw ← not_nonempty_iff_eq_empty at hv1,
    apply hv1,
    use e,
    rw finset.mem_filter,
    exact ⟨mem_univ e,hn⟩,
  }
end

def finite_graph.null_graph (F : finite_graph) : Prop := ∀ v : F.V, F.isolated_vertex v

theorem finite_graph.null_def (F : finite_graph) : F.null_graph ↔ ∀ v : F.V, F.isolated_vertex v:= by refl 

theorem finite_graph.null_only_isolated_vertices (F : finite_graph) : F.null_graph → is_empty F.E :=
begin 
  intro p,
  rw is_empty_iff,
  intro e,
  rw F.null_def at p,
  have he : ∃ v w : F.V, F.edge e = ⟦(v,w)⟧,
  {
    induction F.edge e,
    use [a.fst,a.snd],
    simp,
    refl,
    refl,
  },
  rcases he with ⟨v,w,hvw⟩,
  specialize p v e,
  finish,
end

end finite_graph 

section morphism

variables {F : finite_graph} {K : finite_graph} {H : finite_graph}

structure finite_graph.morphism (F : finite_graph) (G : finite_graph) :=
(aᵥ : F.V → G.V)
(aₑ : F.E → G.E)
(commute : G.edge ∘ aₑ = map (aᵥ) ∘ F.edge)

def finite_graph.id (F : finite_graph) : F.morphism F :=
{
  aᵥ := id,
  aₑ := id,
  commute := by rw [sym2.map_id, comp.right_id,comp.left_id],
}

def finite_graph.comp (g : K.morphism H) (f : F.morphism K)  : F.morphism H := 
{
  aᵥ := g.aᵥ ∘ f.aᵥ,
  aₑ:= g.aₑ ∘ f.aₑ
,
  commute := 
  begin 
    rw ← comp.assoc,
    rw g.commute,
    rw comp.assoc,
    rw f.commute,
    rw ← comp.assoc,
    rw ← map_comp,
  end
}

infixr ` ∘ `: 90  := finite_graph.comp

structure finite_graph.equiv (F : finite_graph) (H : finite_graph) :=
(to_fun : F.morphism H)
(inv_fun : H.morphism F)
(left_inv : to_fun ∘ inv_fun = H.id)
(right_inv : inv_fun ∘ to_fun = F.id)

infixr ` ≃ `: 50  := finite_graph.equiv 

theorem finite_graph.isom_graphs_same_number_of_vertices (bij : F ≃ H) :
fintype.card F.V = fintype.card H.V :=
begin 
  rw fintype.card_eq,
  constructor,
  constructor,
  have hn := bij.right_inv,
  unfold finite_graph.comp finite_graph.id at hn,
  injections_and_clear,
  swap 3,
  apply bij.to_fun.aᵥ,
  swap 3,
  apply bij.inv_fun.aᵥ,
  intro x,
  rw ← comp_app bij.inv_fun.aᵥ,
  rw h_1,exact id.def x,
  have hn := bij.left_inv,
  unfold finite_graph.comp finite_graph.id at hn,
  injections_and_clear,
  intro x,
  rw ← comp_app bij.to_fun.aᵥ,
  rw h_1,exact id.def x,
end

theorem finite_graph.isom_graphs_same_number_of_edges (bij : F ≃ H) :
fintype.card F.E = fintype.card H.E :=
begin 
  rw fintype.card_eq,
  constructor,
  constructor,
  have hn := bij.right_inv,
  unfold finite_graph.comp finite_graph.id at hn,
  injections_and_clear,
  swap 3,
  apply bij.to_fun.aₑ,
  swap 3,
  apply bij.inv_fun.aₑ,
  intro x,
  rw ← comp_app bij.inv_fun.aₑ,
  rw h_2,exact id.def x,
  have hn := bij.left_inv,
  unfold finite_graph.comp finite_graph.id at hn,
  injections_and_clear,
  intro x,
  rw ← comp_app bij.to_fun.aₑ,
  rw h_2,exact id.def x,
end
end morphism
section subgraph

variables {F : finite_graph}

structure finite_graph.subgraph (F : finite_graph) :=
(sub_vertices : finset F.V)
(sub_edges : finset F.E)
(same_vertices : ∀ e ∈ sub_edges, ∀ v ∈ F.edge e, v ∈ sub_vertices)

instance lift_sym2 {H : finite_graph} {h : H.subgraph} : has_lift (sym2 h.sub_vertices) (sym2 H.V) :=
begin 
  constructor,
  intro pa,
  induction pa with p p1 p2 hp,
  apply quot.mk,
  exact ⟨p.fst,p.snd⟩,
  simp,
  apply quot.sound,
  cases p2 with a2 b2, cases p1 with a1 b1,
  simp,
  cases hp,
  constructor,
  constructor,
end

instance finite_graph.sb_to_graph : has_lift (F.subgraph) (finite_graph) :=
begin 
  constructor,
  intro H,
  split, swap 5,
  {
    split, swap,
    exact H.sub_vertices, swap,
    exact H.sub_edges,
    intro e,
    apply fintype.choose (λp : sym2 (H.sub_vertices),↑p = F.edge e),
    have he := H.same_vertices e.1 e.2,
    revert he,
    induction (F.edge ↑e) with pv pv1 pv2 hpv,
    induction pv with v1 v2,
    swap,
    refine congr_fun rfl,
    intros v1 v2 h,
    have h1 := h v1 (mk_has_mem v1 v2),
    have h2 := h v2 (mk_has_mem_right v1 v2),
    apply exists_unique.intro,
    swap 3,
    exact ⟦(⟨v1,h1⟩,⟨v2,h2⟩)⟧,
    solve_by_elim,
    clear e h,
    intros p hp,
    induction p with pr,
    induction pr with a b,
    apply eq_iff.2,
    have hpp := eq_iff.1 hp,
    simp at hpp,
    finish,
    exact rfl,
  },
  all_goals {simp},
  any_goals {apply subtype.fintype},
  any_goals {apply subtype.decidable_eq}, 
end

def finite_graph.top_subgraph (F : finite_graph) : F.subgraph :=
{
  sub_vertices := univ,
  sub_edges := univ,
  same_vertices := 
  begin 
    intros e he v hve,
    exact mem_univ v,
  end
}
end subgraph

section walk
variables {F : finite_graph}

def finite_graph.incid (F : finite_graph) (v w : F.V) : Prop := ∃ e : F.E, F.edge e = ⟦(v,w)⟧

theorem finite_graph.incid_def (F : finite_graph) (v w : F.V) : 
F.incid v w ↔ ∃ e : F.E, F.edge e = ⟦(v,w)⟧ := by refl

def finite_graph.get_edge_from_incid (F : finite_graph) {v w : F.V} {hf : F.simple} :
(F.incid v w) → F.E :=
begin 
  intro h,
  rw F.incid_def at h,
  apply fintype.choose (λ e,F.to_graph.edge e = ⟦(v,w)⟧),
  simp,
  apply F.to_graph.exists_unique_edge_simple_graph,
  exact h,
  exact hf,
end


def inc_prop {V E : Type} (P : V → V → E → Prop) : list V → list E → Prop 
  | [] := λ le, false
  | (a :: []) := λ le,le.empty
  | (a :: b :: lv) := λ le, match le with 
                            | [] := false
                            | e::es := P a b e ∧ (inc_prop (b::lv) es) end

lemma inc_prop_empty_lv {V E : Type} (P : V → V → E → Prop) : ∀ le : list E,
inc_prop P [] le = false :=
begin 
  intro le,
  induction le with x xs hxs,
  unfold inc_prop,
  unfold inc_prop,
end

lemma inc_prop_empty_le {V E : Type} (P : V → V → E → Prop) : ∀ lv : list V,
inc_prop P lv [] = (lv.length = 1) :=
begin 
  intro lv,
  induction lv with x xs hxs,
  simp,
  unfold inc_prop,
  tauto,
  induction xs with y ys hys,
  {
    unfold inc_prop,
    simp,
  },
  {
    unfold inc_prop,
    simp,
  }
end

structure finite_graph.walk (F : finite_graph) :=
(lᵥ : list F.V)
(lₑ : list F.E)
(is_adj : inc_prop (λ v w e, F.edge e = ⟦(v,w)⟧) lᵥ lₑ)

theorem finite_graph.walk.nempty_lᵥ (w : F.walk) : ¬ (w.lᵥ = []) :=
begin 
  intro h,
  have h' := w.is_adj,
  rw h at h',
  convert h',
end

lemma inc_prop_diff_one {V E : Type} {P : V → V → E → Prop} : ∀ lv : list V, ∀ le : list E,
inc_prop P lv le → lv.length = le.length + 1 :=
begin 
  intros lv,
  induction lv with v tv hv,
  {
    intros le hve,
    exfalso,
    convert hve,
  },
  {
    induction tv with w tvv hvv,
    {
      intros le hve,
      induction le with e te he,
      refl,
      exfalso,
      convert hve, symmetry,
      tauto,
    },
    {
      intros le' hve',
      induction le' with e te he,
      tauto,
      rw list.length_cons,
      congr' 1,
      apply hv,
      exact hve'.right,
    }
  }
end

theorem finite_graph.walk.lengths_diff_one (w : F.walk) : w.lᵥ.length = w.lₑ.length + 1 := 
inc_prop_diff_one w.lᵥ w.lₑ (w.is_adj)

def finite_graph.walk.start (w : F.walk) : F.V := begin
  haveI : inhabited F.V,
  {
    constructor,
    apply list.choose (λv:F.V,true) w.lᵥ,
    simp,
    have h := w.nempty_lᵥ,
    revert h,
    induction w.lᵥ,
    case list.nil
    { simp, },
    case list.cons : hd tl ih
    { intro h,
      use hd,
      finish, },
  },
  exact w.lᵥ.head,
end

def finite_graph.walk.end (w : F.walk) : F.V := begin
  haveI : inhabited F.V,
  {
    constructor,
    apply list.choose (λv:F.V,true) w.lᵥ,
    simp,
    have h := w.nempty_lᵥ,
    revert h,
    induction w.lᵥ,
    case list.nil
    { simp, },
    case list.cons : hd tl ih
    { intro h,
      use hd,
      finish, },
  },
  exact w.lᵥ.ilast,
end

def finite_graph.walk.closed (w : F.walk) : Prop := w.start = w.end ∧ w.lᵥ.length > 1

def finite_graph.list_gives_walk (F : finite_graph) : list F.V → Prop 
  | [] := false 
  | (v::[]) := true 
  | (v::v'::lv) := F.incid v v' ∧ finite_graph.list_gives_walk (v'::lv)

lemma finite_graph.list_gives_walk_sublist (F : finite_graph) [inhabited F.V] : 
∀ v : F.V,∀ l : list F.V,
l ≠ nil → ((F.list_gives_walk (v::l)) ↔ (F.incid v l.head ∧ F.list_gives_walk l)):=
begin 
  intros v l,
  induction l with x xs hxs,
  {
    intro h,
    exfalso,
    exact h rfl,
  },
  {
    intros h,
    split,
    {
      intro h',
      unfold finite_graph.list_gives_walk at h',
      exact h',
    },
    {
      rintro ⟨h1,h2⟩,
      unfold finite_graph.list_gives_walk,
      split,
      exact h1,
      exact h2,
    }
  }
end

lemma finite_graph.list_gives_walk_infix (F : finite_graph) {l : list F.V} {h : F.list_gives_walk l} :
∀ l' : list F.V, l' <:+: l → l' ≠ nil → F.list_gives_walk l' :=
begin 
  intros l' hl',
  induction l' with x xs hxs,
  {
    intro h,
    contradiction,
  },
  {
    intro h,clear h,
    by_cases hs : xs = nil,
    {
      rw hs,
      unfold finite_graph.list_gives_walk,
    },
    haveI : inhabited F.V := ⟨x⟩,
    rw F.list_gives_walk_sublist,
    swap,
    exact hs,
    split,swap,
    {
      apply hxs,
      apply is_infix.trans,
      swap 3,
      exact (x::xs),
      apply infix_cons,
      refl,
      exact hl',
      exact hs,
    },
    {
      induction l with y ys hys,
      rw eq_nil_iff_infix_nil at hl',
      contradiction,
      induction ys with z zs hzs,
      {
        replace hl' := length_le_of_infix hl',
        simp at hl',
        replace hs := length_pos_iff_ne_nil.2 hs,
        linarith,
      },
      {
        unfold finite_graph.list_gives_walk at h,
        by_cases hxy : x = y ∧ xs.head = z,
        {
          cases hxy with hxy1 hxy2,
          rw [hxy1,hxy2],
          exact h.1,
        },
        {
          apply hys,
          {
            intros h1 h2,
            clear h2,
            apply hxs,
            {
              transitivity x::xs,
              apply infix_cons,
              refl,
              exact hl',
            },
            exact hs,
          },
          {
            rw infix_iff_prefix_suffix at hl' ⊢,
            rcases hl' with ⟨t,ht,ht'⟩,
            use t,
            split,
            exact ht,
            rw suffix_cons_iff at ht',
            cases ht' with ht' ht',
            swap,
            exact ht',
            rw ht' at ht,
            rw cons_prefix_iff at ht,
            simp at hxy,
            specialize hxy ht.1,
            rw ht.1 at *,
            replace ht := ht.2,
            exfalso,
            apply hxy,
            clear hys hzs hxs,
            induction xs with u us hus,
            contradiction,
            simp,
            rw cons_prefix_iff at ht,
            exact ht.1,
          },
          exact h.2,
        }
      }
    }
  }
end

lemma finite_graph.list_gives_walk_from_walk (F : finite_graph) :
∀ w : F.walk,  F.list_gives_walk w.lᵥ :=
begin 
  intro w,
  have hw := w.is_adj,
  obtain ⟨lv,hv⟩ : {lv : list F.V // w.lᵥ = lv} := ⟨_, rfl⟩,
  obtain ⟨le,he⟩ : {le : list F.E // w.lₑ = le} := ⟨_, rfl⟩,
  rw hv at hw ⊢,
  rw he at hw,
  clear hv he w,
  revert le,
  induction lv with v lv hlv,
  {
    unfold inc_prop,
    tauto,
  },
  {
    induction lv with v' lv' hlv',
    {
      unfold inc_prop,
      tauto,
    },
    {
      intro le,
      induction le with e le hle,
      {
        unfold inc_prop,
        tauto,
      },
      {
        intro h,
        unfold inc_prop at h,
        clear hle hlv',
        unfold finite_graph.list_gives_walk,
        split,
        {
          use e,
          exact h.1,
        },
        {
          apply hlv,
          exact h.2,
        }
      }
    }
  }
end

def finite_graph.get_list_edges (F : finite_graph) (hs : F.simple) :
 Π l : list F.V, (F.list_gives_walk l → list F.E)
 | [] := λp, []
 | [v] := λp, []
 | (v::v'::lv) := λp, ((@finite_graph.get_edge_from_incid) F v v' hs (and.left p))::
 ((finite_graph.get_list_edges (v'::lv)) p.right)

lemma finite_graph.inc_prop_from_list_vertices (l : list F.V) (h : F.list_gives_walk l) (hs : F.simple) : 
∃ p : inc_prop (λ v w e, F.edge e = ⟦(v,w)⟧) l ((F.get_list_edges hs l) h),true :=
begin 
  induction l with v lv hlv,
  {
    solve_by_elim,
  },
  {
    induction lv with w lw hlw,
    {
      constructor,
      unfold inc_prop,
      solve_by_elim,
      exact trivial,
    },
    {
      constructor,
      unfold finite_graph.get_list_edges,
      unfold inc_prop,
      split,
      {
        unfold finite_graph.get_edge_from_incid,
        apply fintype.choose_spec (λe:F.E,F.edge e = ⟦(v,w)⟧)
        (F.to_graph.exists_unique_edge_simple_graph _),
        exact hs,
        unfold finite_graph.list_gives_walk at h,
        apply h.left,
      },
      {
        unfold finite_graph.list_gives_walk at h,
        specialize hlv h.right,
        cases hlv with p hp,
        exact p,
      },
      exact trivial,
    }
  }
end


structure finite_graph.path (F : finite_graph) extends finite_graph.walk F :=
(vertex_unicity : lᵥ.nodup)
(is_open : ¬ to_walk.closed)

def finite_graph.path.length (p : F.path) : ℕ := p.lₑ.length

structure finite_graph.circuit (F : finite_graph) extends finite_graph.walk F :=
(vertex_unicity : (lᵥ.tail).nodup)
(is_closed : to_walk.closed)

def finite_graph.path.start (p : F.path) : F.V := p.to_walk.start

def finite_graph.path.end (p : F.path) : F.V := p.to_walk.end

def finite_graph.are_connected (F : finite_graph) (v v' : F.V) : Prop :=
 ∃ w : F.walk, w.start = v ∧ w.end = v' 

theorem finite_graph.are_connected_def (v v' : F.V) : 
F.are_connected v v' ↔ ∃ w : F.walk, w.start = v ∧ w.end = v' := by refl

lemma finite_graph.rmv_unt_aux_gives_walk (F : finite_graph) : ∀ v : F.V, ∀ l : list F.V,
F.list_gives_walk l →  (F.list_gives_walk (rmv_unt_aux v l) ∨ (rmv_unt_aux v l) = nil) :=
begin 
  intros v l hl,
  induction l with x xs hxs,
  {
    unfold rmv_unt_aux,
    right, refl,
  },
  {
    unfold rmv_unt_aux,
    split_ifs, swap,
    {
      left,
      exact hl,
    },
    {
      induction xs with y ys hys,
      {
        unfold rmv_unt_aux,
        right, refl,
      },
      {
        unfold finite_graph.list_gives_walk at hl,
        cases hxs hl.2 with h' h',
        left,
        exact h',
        right,
        exact h',
      }
    }
  }
end

lemma finite_graph.rmv_unt_aux_gives_walk' (F : finite_graph) [inhabited F.V] : 
∀ v : F.V, ∀ l : list F.V,
F.list_gives_walk l → F.incid v l.head 
→  (F.list_gives_walk (v::rmv_unt_aux v l)) :=
begin 
  intros v l,
  induction l with x xs hxs,
  {
    intros h h',
    unfold rmv_unt_aux,
  },
  {
    intros h h',
    unfold rmv_unt_aux,
    split_ifs, swap,
    {
      unfold finite_graph.list_gives_walk,
      split, swap, exact h,
      apply h',
    },
    {
      by_cases hs : rmv_unt_aux v xs = nil,
      rw hs,
      unfold finite_graph.list_gives_walk,
      have hn := rmv_aux_suffix v xs,
      cases hn with hn hn,
      swap,
      {
        apply finite_graph.list_gives_walk_infix,
        swap 4,
        exact xs,
        swap,
        apply infix_of_suffix hn,
        swap,
        simp,
        rw F.list_gives_walk_sublist at h,
        exact h.2,
        intro hc,
        apply hs,
        rw hc,
        unfold rmv_unt_aux,
      },
      rw hn,
      suffices : v = x,
      rw this,
      exact h,
      rw mem_cons_iff at h_1,
      cases h_1 with hx hx,
      exact hx,
      rw rmv_aux_eq at hn,
      contradiction,
    }
  }
end

lemma finite_graph.rmv_unt_gives_walk (F : finite_graph) [inhabited F.to_graph.V] : 
∀ l : list F.V, F.list_gives_walk l →  F.list_gives_walk (rmv_unt l) :=
begin 
  intros l hl,
  obtain ⟨n, hn⟩ : {n : ℕ // l.length = n} := ⟨_, rfl⟩,
  revert l,
  apply nat.strong_induction_on n,
  intros m hm l hl,
  induction l with x xs hxs,
  {
    intro h,
    unfold rmv_unt,
    exact hl,
  },
  {
    intro h,
    unfold rmv_unt,
    by_cases hs : xs = nil,
    {
      rw hs at *,
      unfold rmv_unt_aux,
      unfold rmv_unt,
    },
    {
      clear hxs,
      by_cases hss : rmv_unt (rmv_unt_aux x xs) = nil,
      {
        rw hss,
        unfold finite_graph.list_gives_walk,
      },
      {
        rw finite_graph.list_gives_walk_sublist at hl ⊢,
        swap 3,
        exact hs,
        swap,
        exact hss,
        split,
        swap,
        {
          apply hm,
          swap 4,
          exact (rmv_unt_aux x xs).length,
          have hns := rmv_aux_smaller x xs,
          simp at h,
          linarith,
          swap,
          refl,
          cases (F.rmv_unt_aux_gives_walk x xs) hl.2 with h1 h2,
          exact h1,
          rw h2 at hss,
          rw rmv_unt at hss,
          contradiction,
        },
        {
          have hu : (rmv_unt_aux x xs) ≠ nil,
          {
            intro hu,
            rw hu at hss,
            unfold rmv_unt at hss,
            contradiction,
          },
          have ha : (rmv_unt (rmv_unt_aux x xs)).head = (rmv_unt_aux x xs).head,
          {
            revert hu,
            induction (rmv_unt_aux x xs) with y ys hys,
            intro hp,
            contradiction,
            intro hp, clear hp,
            unfold rmv_unt,
            simp,
          },
          rw ha,
          have hb := (F.rmv_unt_aux_gives_walk' x xs) hl.2 hl.1,
          revert hb hu,
          induction (rmv_unt_aux x xs) with y ys hys,
          intros h1 h2,
          contradiction,
          simp,
          unfold finite_graph.list_gives_walk,
          tauto,
        }
      }
    } 
  }
end

set_option trace.check true
theorem finite_graph.are_connected_path (v v' : F.V) (hs : F.simple) : 
F.are_connected v v' ↔ ∃ p : F.path, p.start = v ∧ p.end = v' := 
begin 
  split,swap,
  {
    rintro ⟨p,hp⟩,
    use p.to_walk,
    exact hp,
  },
  {
    intro h,
    cases h with w hw,
    haveI : inhabited F.V := ⟨v⟩,
    have hwl := F.list_gives_walk_from_walk w,
    have hwn := w.nempty_lᵥ,
    have hs1 := rmv_head w.lᵥ hwn,
    unfold finite_graph.walk.start finite_graph.walk.end at hw,
    cases hw with hw1 hw2,
    rw [← hw1,←  hw2],
    clear hw1 hw2 v v',
    constructor,
    swap,
    {
      exact { lᵥ := rmv_unt w.lᵥ,
      lₑ := F.get_list_edges hs (rmv_unt w.lᵥ) (F.rmv_unt_gives_walk w.lᵥ hwl),
      is_adj := 
      begin 
        have hu := finite_graph.inc_prop_from_list_vertices (rmv_unt w.lᵥ) 
        (F.rmv_unt_gives_walk w.lᵥ hwl) hs,
        cases hu with p hp,
        exact p,
      end,
      vertex_unicity := rmv_nodup w.lᵥ,
      is_open :=
      begin 
        unfold finite_graph.walk.closed finite_graph.path.start finite_graph.path.end,
        unfold finite_graph.walk.start finite_graph.walk.end,
        push_neg,
        apply nodup_head_eq_tail_length_1,
        exact rmv_nodup w.lᵥ,
      end },
    },
    split,
    {
      cases hs,
      dsimp at *,
      unfold finite_graph.path.start finite_graph.walk.start,
      simp,
      rw ← rmv_head,
      refl,
    }
    
  }
end 

end walk

end graph

