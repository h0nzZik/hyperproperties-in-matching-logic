From Coq Require Import ssreflect ssrfun ssrbool.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.

From Coq Require Import String Ensembles.
From Coq.Logic Require Import FunctionalExtensionality.
From stdpp Require Import sets.

Require Import ltl.
From MatchingLogic Require Import Logic Theories.Definedness Theories.Sorts SignatureHelper.

Import BoundVarSugar.

Module LTL.
  Import MatchingLogic.Syntax.Notations.
  Import MatchingLogic.Semantics.Notations.
  
  Section LTL.
    (* We are parametrized with a set of atomic proposition. *)
    Context {ltlsig : LTLSignature}.

    Inductive Symbols :=
    | sym_import_definedness (d : Definedness.Symbols)
    | sym_import_sorts (s : Sorts.Symbols)
    | sym_SortTrace
    | sym_SortTraceSuffix
    | sym_next
    | sym_prev
    | sym_a (ap : AP ltlsig)
    .

    Lemma Symbols_dec : forall (s1 s2 : Symbols), {s1 = s2} + {s1 <> s2}.
    Proof.
      decide equality.
      * decide equality.
      * decide equality.
      * apply AP_dec.
    Qed.


    Instance symbols_H : SymbolsH := {| SHSymbols := Symbols; SHSymbols_dec := Symbols_dec; |}.
    Instance signature : Signature := @SignatureFromSymbols symbols_H.
    Arguments signature : simpl never. (* does not really help :-( *)

    Instance definedness_syntax : Definedness.Syntax :=
      {|
         Definedness.inj := sym_import_definedness;
      |}.

    Instance sorts_syntax : Sorts.Syntax :=
      {|
      Sorts.inj := sym_import_sorts;
      Sorts.imported_definedness := definedness_syntax;
      |}.
    
    Notation "A → B" := (patt_imp A B) (at level 99, right associativity, B at level 200) : ml_scope.
    (*
    Notation "A /\ B" := (patt_and A B) (at level 80, right associativity) : ml_scope.
    Notation "A ‌\/ B" := (patt_or A B) (at level 85, right associativity) : ml_scope.
    *)
    Notation "∃, A" := (ex, A) (at level 55) : ml_scope.
    Notation "μ, A" := (mu, A) (at level 55) : ml_scope.
    Notation "A == B" := (patt_equal A B) (at level 100) : ml_scope.
    Notation "A ∈ B" := (patt_in A B) (at level 70) : ml_scope.
    Notation "A ⊆ B" := (patt_subseteq A B) (at level 70) : ml_scope.
    Notation "⊥" := (patt_bott) : ml_scope.

    Notation "[[ A ]]" := (patt_inhabitant_set A) : ml_scope.

    (* Element variables - free *)
    Notation x := (evar "x").
    Notation y := (evar "y").
    Notation z := (evar "z").

    (*
    (* Element variables - bound *)
    Notation b0 := (patt_bound_evar 0).
    Notation b1 := (patt_bound_evar 1).
    *)

    (* TODO move to BoundVarSugar *)
    (* Set variables - bound *)
    Notation B0 := (patt_bound_svar 0).


    Definition patt_partial_function(phi from to : Pattern) : Pattern :=
      patt_forall_of_sort from (patt_exists_of_sort to ((phi $ b1) ⊆ b0)).

    Notation "A : B ⇀ C" := (patt_partial_function A B C) (at level 80) : ml_scope.
    
    Notation Trace := (sym sym_SortTrace).
    Notation TraceSuffix := (sym sym_SortTraceSuffix).

    Definition patt_next (phi : Pattern) : Pattern :=
      patt_app (sym sym_next) phi.
    
    Definition patt_prev (phi : Pattern) : Pattern :=
      patt_app (sym sym_prev) phi.

    
   Lemma evar_open_next db x ϕ: evar_open db x (patt_next ϕ) = patt_next (evar_open db x ϕ).
   Proof. unfold patt_next. auto. Qed.
   Lemma svar_open_next db x ϕ: svar_open db x (patt_next ϕ) = patt_next (svar_open db x ϕ).
   Proof. unfold patt_next. auto. Qed.
   Lemma evar_open_prev db x ϕ: evar_open db x (patt_prev ϕ) = patt_prev (evar_open db x ϕ).
   Proof. unfold patt_prev. auto. Qed.
   Lemma svar_open_prev db x ϕ: svar_open db x (patt_prev ϕ) = patt_prev (svar_open db x ϕ).
   Proof. unfold patt_prev. auto. Qed.
   Hint Rewrite -> evar_open_next svar_open_next evar_open_prev svar_open_prev : ml_db.
   (* TODO typeclass instance *)


   (* TODO nest_mu *)
   Definition patt_until ϕ₁ ϕ₂ := patt_mu (patt_or ϕ₂ (patt_and ϕ₁ (patt_next B0))).
   
    Notation "∘ X" := (patt_next X) (at level 50) : ml_scope.

    Inductive AxiomName :=
    | AxImportedDefinedness (name : Definedness.AxiomName) (* imports axioms from the Definedness module *)
    | AxPrev
    | AxTrace
    | AxTraceSuffix
    (*| AxInf*)
    | AxNextOut
    | AxNextPFun
    | AxNextInj
    | AxPrevTFun
    | AxPrevInj
    | AxAtomicProp (ap : AP ltlsig) (* defines a potentially infinite class of axioms *)
    .

    Definition axiom(name : AxiomName) : @Pattern signature :=
      match name with
      | AxImportedDefinedness name' => Definedness.axiom name'
                                                         
      | AxPrev
          (* TODO make `and` bind tighter than `∃,` *)
        => (patt_prev x == (∃, (b0 and (x ∈ ∘b0 ))))%ml
                                            
      | AxTrace
        => (∃,([[ Trace ]] == b0))%ml
                                         
      | AxTraceSuffix
        => ([[ TraceSuffix ]] == (μ, ([[ Trace ]] or (patt_prev B0))))%ml
(*
      | AxInf
        => ([[ TraceSuffix ]] ⊆ ∘ ([[ TraceSuffix ]]))%ml
*)
      | AxNextOut
        => ((∘(¬([[ TraceSuffix ]]))) ⊆ (¬ [[ TraceSuffix ]]))%ml

      | AxNextPFun
        => (sym sym_next) : TraceSuffix ⇀ TraceSuffix

      | AxNextInj
        => patt_partial_function_injective (sym sym_next) TraceSuffix

      | AxPrevTFun
        => patt_total_function (sym sym_prev) TraceSuffix TraceSuffix
                               
      | AxPrevInj
        => patt_total_function_injective (sym sym_prev) TraceSuffix

      | AxAtomicProp a
        => (sym (sym_a a)) ⊆ [[ TraceSuffix ]]
      end.

    Definition named_axioms : NamedAxioms := {| NAName := AxiomName; NAAxiom := axiom; |}.
    Definition theory := theory_of_NamedAxioms named_axioms.

    Program Definition definedness_axioms_included_in_axioms :=
      @Build_NamedAxiomsIncluded signature Definedness.named_axioms named_axioms AxImportedDefinedness _.
    Next Obligation.
      intros n. simpl. reflexivity.
    Qed.
    
    Lemma satisfies_theory_impl_satisfies_definedness_theory M:
      M ⊨ᵀ theory -> M ⊨ᵀ Definedness.theory.
    Proof.
      intros H.
      apply satisfies_theory_subseteq with (Γ₂ := theory). 2: assumption.
      apply NamedAxiomsIncluded_impl_TheoryIncluded.
      apply definedness_axioms_included_in_axioms.
    Qed.

    Hint Resolve satisfies_theory_impl_satisfies_definedness_theory : core.
    
   
    (* Mnext, Mprev and their properties *)
    Section basics.
      Context {M : Model}.
      Hypothesis M_satisfies_theory : M ⊨ᵀ theory.

      Check sym_next.
      Definition Mnext m := app_ext (sym_interp sym_next) (Ensembles.Singleton (Domain M) m).
      Definition Mnext_ext (A : Power (Domain M)) : Power (Domain M) :=
        fun (e : Domain M) => exists (m : Domain M), Ensembles.In (Domain M) A m /\ Ensembles.In (Domain M) (Mnext m) e.

      Definition Mprev m := app_ext (sym_interp sym_prev) (Ensembles.Singleton (Domain M) m).
      Definition Mprev_ext (A : Power (Domain M)) : Power (Domain M) :=
        fun (e : Domain M) => exists (m : Domain M), Ensembles.In (Domain M) A m /\ Ensembles.In (Domain M) (Mprev m) e.
      Definition MTrace ρₑ ρₛ := @pattern_interpretation _ M ρₑ ρₛ [[ Trace ]].
      Definition MTrSuf ρₑ ρₛ := @pattern_interpretation _ M ρₑ ρₛ [[ TraceSuffix ]].
      

      (* TODO generalized version in the library *)
      Lemma Mnext_Mprev_inversions : forall (m1 m2 : Domain M),
          Ensembles.In (Domain M) (Mnext m2) m1 <-> Ensembles.In (Domain M) (Mprev m1) m2.
      Proof.
        pose proof (Hprev := satisfies_theory_impl_satisfies_named_axiom M_satisfies_theory AxPrev).
        cbn in Hprev.
        unfold satisfies_model in Hprev.
        intros.
        remember ((fun x : evar_name => m1)) as evar_val.
        remember (fun X : svar_name => Empty_set (Domain M)) as svar_val.
        specialize (Hprev evar_val svar_val).
        apply equal_iff_interpr_same in Hprev. 2: auto.
        unfold Same_set in Hprev. unfold Included in Hprev. unfold In in Hprev.
        unfold patt_prev in Hprev.
        rewrite pattern_interpretation_app_simpl in Hprev.
        unfold sym in Hprev.
        rewrite pattern_interpretation_sym_simpl in Hprev.
        unfold LTL.x in Hprev.
        rewrite pattern_interpretation_free_evar_simpl in Hprev.
        fold LTL.x in Hprev. subst. simpl in Hprev.
        fold (Mprev m1) in Hprev.

        remember ((fun x : evar_name => m1)) as evar_val.
        remember (fun X : svar_name => Empty_set (Domain M)) as svar_val.
        pose proof (Hbuild := @pattern_interpretation_set_builder signature M (x ∈ ∘ b0) evar_val svar_val).
        cbn zeta in Hbuild.
        fold signature in *.
        rewrite -> Hbuild in Hprev.
        2: { unfold signature in *.
             autorewrite with ml_db. simpl.
             apply T_predicate_in. auto.
        }
        
        (* TODO make `simpl` not simplify ands, ors etc to implications *)
        (* TODO make a hint database to solve M_predicate goals *)
        (* TODO solve M |= theory automatically *)
        autorewrite with ml_db in Hprev.

        (* simplify Hprev, but not too much *)
        cbn delta in Hprev.
        move: Hprev.
        rewrite [PeanoNat.Nat.eqb 0 0]/=.
        cbv iota.
        move=> Hprev.
        clear Hbuild.

        unfold Ensembles.In.
        rewrite -> Hprev.
        Check free_evar_in_patt.
        (*autorewrite with ml_db.*)
        (*simpl.*)
        (*unfold fresh_evar at 3.*)
        Search evar_open patt_in.
        unfold signature in *.
        (*rewrite -> evar_open_in.*)
        (*Set Printing Implicit.*)
        remember (evar_open 0 (fresh_evar (x ∈ ∘ b0)) x) as y.
        unfold signature in Heqy. (* This is really annoying! *)
        rewrite <- Heqy. (* just a test *)
        rewrite -> Heqy.
        unfold x at 3.
        rewrite -> evar_open_free_evar.
        rewrite <- free_evar_in_patt. 2: auto.
        rewrite [∘ patt_free_evar _] /patt_next.
        rewrite -> pattern_interpretation_app_simpl.
        rewrite /Mnext.
        unfold sym.
        rewrite -> pattern_interpretation_sym_simpl.
        unfold In.
        rewrite -> pattern_interpretation_free_evar_simpl.
        rewrite -> update_evar_val_same.
        
        unfold fresh_evar. simpl.
        repeat rewrite -> union_empty_r_L.
        rewrite -> union_empty_l_L.
        rewrite -> update_evar_val_neq.
        2: {
          eapply extralibrary.notin_cons_l.
          apply find_fresh_evar_name'_is_fresh.
        }
        subst evar_val. unfold Ensembles.In. auto.
      Qed.

      (* We may use this to represent partial functions *)
      Definition empty_or_singleton S := S = Empty \/ exists m', S = Ensembles.Singleton (Domain M) m'.

      Lemma MTrace_independent ρₑ₁ ρₛ₁ ρₑ₂ ρₛ₂:
        MTrace ρₑ₁ ρₛ₁ = MTrace ρₑ₂ ρₛ₂.
      Proof.
        rewrite /MTrace.
        rewrite /patt_inhabitant_set.
        rewrite 2!pattern_interpretation_app_simpl.
        rewrite /Sorts.sym.
        unfold Trace.
        rewrite !pattern_interpretation_sym_simpl.
        reflexivity.
      Qed.

      Lemma MTrSuf_independent ρₑ₁ ρₛ₁ ρₑ₂ ρₛ₂:
        MTrSuf ρₑ₁ ρₛ₁ = MTrSuf ρₑ₂ ρₛ₂.
      Proof.
        rewrite /MTrSuf.
        rewrite /patt_inhabitant_set.
        rewrite 2!pattern_interpretation_app_simpl.
        rewrite /Sorts.sym.
        unfold Trace.
        rewrite !pattern_interpretation_sym_simpl.
        reflexivity.
      Qed.      
      
    End basics.

    (* Conversion function *)
    Fixpoint L2M (f: @ltl.Formula ltlsig) : Pattern :=
      match f with
      | f_atomic a => sym (sym_a a)
      | f_neg f' => patt_not (L2M f')
      | f_and f₁ f₂ => patt_and (L2M f₁) (L2M f₂)
      | f_next f' => patt_next (L2M f')
      | f_until f₁ f₂ => patt_until (L2M f₁) (L2M f₂)
      end.

    Section with_model.
      Context {M : Model}.
      Hypothesis M_satisfies_theory : M ⊨ᵀ theory.

    End with_model.
    
  End LTL.

End LTL.
