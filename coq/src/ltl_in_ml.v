From Coq Require Import ssreflect ssrfun ssrbool.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.

From Coq Require Import String Ensembles.
From Coq.Logic Require Import FunctionalExtensionality.
From stdpp Require Import sets.

Require Import ltl.
From MatchingLogic Require Import Logic DerivedOperators Theories.Definedness Theories.Sorts SignatureHelper.

Import BoundVarSugar.

Module LTL.
  Import MatchingLogic.Syntax.Notations.
  Import MatchingLogic.Semantics.Notations.
  Import MatchingLogic.DerivedOperators.Notations.
  
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


    Instance symbols_H : SymbolsH Symbols := {| SHSymbols_eqdec := Symbols_dec; |}.
    Instance signature : Signature := @SignatureFromSymbols _ symbols_H.
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
    | AxNoConfusion
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
        (* => (patt_prev x == (∃, (b0 and (x ∈ ∘b0 ))))%ml*)
        => patt_eq_inversion_of (sym sym_prev) (sym sym_next)
                                            
      | AxTrace
        => (∃,([[ Trace ]] == b0))%ml
                                         
      | AxTraceSuffix
        => ([[ TraceSuffix ]] == (μ, ([[ Trace ]] or (patt_prev B0))))%ml
(*
      | AxInf
        => ([[ TraceSuffix ]] ⊆ ∘ ([[ TraceSuffix ]]))%ml
 *)
      | AxNoConfusion
        => ([[ Trace ]] and (patt_prev [[ TraceSuffix ]])) == ⊥
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
        pose proof (Hprev := proj1 (satisfies_theory_iff_satisfies_named_axioms named_axioms M) M_satisfies_theory AxPrev).
        cbn in Hprev.
        unfold satisfies_model in Hprev.
        intros.
        remember ((fun x : evar_name => m1)) as evar_val.
        remember (fun X : svar_name => Empty_set (Domain M)) as svar_val.
        specialize (Hprev evar_val svar_val).
        unfold patt_eq_inversion_of in Hprev.
      Abort.
      
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
    Fixpoint L2M_ϕ (f: @ltl.Formula ltlsig) : Pattern :=
      match f with
      | f_atomic a => sym (sym_a a)
      | f_neg f' => patt_not (L2M_ϕ f')
      | f_and f₁ f₂ => patt_and (L2M_ϕ f₁) (L2M_ϕ f₂)
      | f_next f' => patt_next (L2M_ϕ f')
      | f_until f₁ f₂ => patt_until (L2M_ϕ f₁) (L2M_ϕ f₂)
      end.

    
    Section ltlmodeltomlmodel.
      Context {LM : @ltl.Model ltlsig}.

      Inductive L2M_Carrier :=
      | car_nat (n : nat)
      | car_def | car_inh | car_Trace
      | car_TrSuf | car_next | car_prev.

      Lemma L2M_Carrier_eqdec : EqDecision L2M_Carrier.
      Proof.
        intros x y.
        unfold Decision.
        decide equality.
        decide equality.
      Qed.

      Definition L2M_sym_interp (sym : Symbols) : Ensemble L2M_Carrier :=
        match sym with
        | sym_import_definedness definedness
          => Ensembles.Singleton _ car_def
        | sym_import_sorts inhabitant
          => Ensembles.Singleton _ car_inh
        | sym_SortTrace
          => Ensembles.Singleton _ car_Trace
        | sym_SortTraceSuffix
          => Ensembles.Singleton _ car_TrSuf
        | sym_next
          => Ensembles.Singleton _ car_next
        | sym_prev
          => Ensembles.Singleton _ car_prev
        | sym_a a
          => fun m =>
               match m with
               | car_nat n => LM n a
               | _ => False
               end
        end.

      Definition L2M_app_interp (x y : L2M_Carrier) : Ensemble L2M_Carrier :=
        match x, y with
        | car_def, _
          => Full_set _
               
        | car_inh, car_Trace
          => fun m =>
               match m with
               | car_nat n => n = 0
               | _ => False
               end
        | car_inh, car_TrSuf
          => fun m =>
               match m with
               | car_nat _ => True
               | _ => False
               end

        | car_next, car_nat 0
          => Empty_set _

        | car_next, car_nat (S n)
          => Ensembles.Singleton _ (car_nat n)

        | car_prev, car_nat n
          => Ensembles.Singleton _ (car_nat (S n))
          
        | _, _ => Empty_set _
        end.

      Definition L2M_Mod : Model :=
        {| Domain := L2M_Carrier ;
           nonempty_witness := car_def ;
           Domain_eq_dec := L2M_Carrier_eqdec ;
           app_interp := L2M_app_interp ;
           sym_interp := L2M_sym_interp ;
        |}.


      Lemma L2M_Mod_satisfies_definedness_named:
        L2M_Mod ⊨ᴹ Definedness.axiom AxDefinedness.
      Proof.
        apply single_element_definedness_impl_satisfies_definedness.
        exists car_def. simpl. auto.
      Qed.
      
      Lemma L2M_Mod_satisfies_definedness_theory: L2M_Mod ⊨ᵀ Definedness.theory.
      Proof.
        unfold Definedness.theory.
        Search theory_of_NamedAxioms.
        apply satisfies_theory_iff_satisfies_named_axioms.
        intros n. destruct n.
        apply L2M_Mod_satisfies_definedness_named.
      Qed.

      Lemma L2M_Mod_satisfies_axiom_prev:
        L2M_Mod ⊨ᴹ patt_eq_inversion_of (sym sym_prev) (sym sym_next).
      Proof.
          unfold "⊨ᴹ".
          intros ρₑ ρₛ.
          apply pattern_interpretation_eq_inversion_of.
          { apply L2M_Mod_satisfies_definedness_theory. }
          intros m₁ m₂.
          unfold rel_of.
          rewrite 2!pattern_interpretation_sym_simpl.
          simpl.
          unfold app_ext.
          split.
          + intros [le [m [H1 [H2 H3] ] ] ].
            inversion H1. inversion H2. subst. clear H1 H2.
            simpl in H3.
            exists car_next. simpl.
            exists m₂.
            split.
            { constructor. }
            split.
            { constructor. }
            destruct m,m₂; try inversion H3.
            constructor.
          + intros [le [re [H1 [H2 H3 ] ] ] ].
            inversion H1. inversion H2. subst. clear H1 H2.
            simpl in H3.
            exists car_prev. exists m₁. simpl.
            split.
            { constructor. }
            split.
            { constructor. }
            destruct re,m₁; try destruct n; try inversion H3.
            constructor.
      Qed.

      Lemma L2M_Mod_satisfies_axiom_trace:
        L2M_Mod ⊨ᴹ (∃, ([[Trace]] == b0)).
      Proof.
        intros ρₑ ρₛ.
        Search pattern_interpretation patt_exists Full.
        rewrite pattern_interpretation_exists_predicate_full.
        2: { rewrite simpl_evar_open.
             apply T_predicate_equals.
             apply L2M_Mod_satisfies_definedness_theory.
        }
        exists (car_nat 0).
        remember (fresh_evar ([[Trace]] == b0)) as x.
        rewrite -Heqx.
        rewrite simpl_evar_open.
        rewrite [evar_open 0 x b0]/=.
        Search pattern_interpretation patt_equal Full.
        rewrite equal_iff_interpr_same.
        2: { apply L2M_Mod_satisfies_definedness_theory. }
        rewrite [evar_open 0 x [[Trace]]]/=.
        rewrite pattern_interpretation_free_evar_simpl.
        rewrite pattern_interpretation_app_simpl.
        rewrite 2!pattern_interpretation_sym_simpl.
        simpl.
        unfold app_ext.
        apply Ensembles_Ext.Same_set_to_eq.
        split.
        - intros e [e1 [e2 [H1 [H2 H3] ] ] ].
          inversion H1. inversion H2. clear H1 H2. subst.
          unfold Ensembles.In.
          rewrite update_evar_val_same.
          simpl in H3. destruct e; subst; try constructor; try inversion H3.
        - intros e H.
          inversion H. clear H. subst e.
          rewrite update_evar_val_same.
          unfold Ensembles.In.
          exists car_inh. exists car_Trace.
          split.
          { constructor. }
          split.
          { constructor. }
          simpl.
          reflexivity.
      Qed.        
      
      Lemma L2M_Mod_satisfies_theory : L2M_Mod ⊨ᵀ theory.
      Proof.
        apply satisfies_theory_iff_satisfies_named_axioms.
        intros n. unfold named_axioms in n. simpl in n.
        destruct n.
        - (* Definedness *)
          simpl.
          destruct name.
          apply L2M_Mod_satisfies_definedness_named.
        - (* Prev *)
          simpl.
          apply L2M_Mod_satisfies_axiom_prev.
        - (* Trace *)
          simpl.
          apply L2M_Mod_satisfies_axiom_trace.

      Abort.

    End ltlmodeltomlmodel.
    
    
    Section with_model.
      Context {M : Model}.
      Hypothesis M_satisfies_theory : M ⊨ᵀ theory.

    End with_model.
    
  End LTL.

End LTL.
