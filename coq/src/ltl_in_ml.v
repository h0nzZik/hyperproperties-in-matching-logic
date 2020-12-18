From Coq Require Import String Ensembles.
Require Import ltl.
From MatchingLogic Require Import Logic Theories.Definedness Theories.Sorts SignatureHelper.


Print Model.

Module LTL.
  Import MatchingLogic.Syntax.Notations.
  Import MatchingLogic.Semantics.Notations.

  (* Should this be a type class too? *)
  Record LTLSignature :=
    { AP : Set;
      AP_dec : forall (a1 a2 : AP), {a1 = a2} + {a1 <> a2};
    }.
  
  
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
      * apply (AP_dec ltlsig).
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
    
    Notation "A → B" := (patt_imp A B) (at level 90, right associativity, B at level 200) : ml_scope.
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

    Notation "[[ A ]]" := (inhabitant_set A) : ml_scope.

    (* Element variables - free *)
    Notation x := (evar "x").
    Notation y := (evar "y").
    Notation z := (evar "z").

    (* Element variables - bound *)
    Notation b0 := (patt_bound_evar 0).
    Notation b1 := (patt_bound_evar 1).

    (* Set variables - bound *)
    Notation B0 := (patt_bound_svar 0).


    Definition patt_partial_function(phi from to : Pattern) : Pattern :=
      patt_forall_of_sort from (patt_exists_of_sort to ((phi $ b1) ⊆ b0)).

    Notation "A : B ⇀ C" := (patt_partial_function A B C) (at level 80) : ml_scope.
    
    Notation Trace := (sym sym_SortTrace).
    Notation TraceSuffix := (sym sym_SortTraceSuffix).

    Definition next (phi : Pattern) : Pattern :=
      patt_app (sym sym_next) phi.
    
    Definition prev (phi : Pattern) : Pattern :=
      patt_app (sym sym_prev) phi.

    
   Lemma evar_open_next db x ϕ: evar_open db x (next ϕ) = next (evar_open db x ϕ).
   Proof. unfold next. auto. Qed.
   Lemma svar_open_next db x ϕ: svar_open db x (next ϕ) = next (svar_open db x ϕ).
   Proof. unfold next. auto. Qed.
   Lemma evar_open_prev db x ϕ: evar_open db x (prev ϕ) = prev (evar_open db x ϕ).
   Proof. unfold prev. auto. Qed.
   Lemma svar_open_prev db x ϕ: svar_open db x (prev ϕ) = prev (svar_open db x ϕ).
   Proof. unfold prev. auto. Qed.
   Hint Rewrite -> evar_open_next svar_open_next evar_open_prev svar_open_prev : ml_db.
    
    Notation "∘ X" := (next X) (at level 50) : ml_scope.

    Inductive AxiomName :=
    | AxImportedDefinedness (name : Definedness.AxiomName) (* imports axioms from the Definedness module *)
    | AxPrev
    | AxTrace
    | AxTraceSuffix
    | AxInf
    | AxNextOut
    | AxNextPFun
    | AxNextInj
    | AxAtomicProp (ap : AP ltlsig) (* defines a potentially infinite class of axioms *)
    .

    Definition axiom(name : AxiomName) : @Pattern signature :=
      match name with
      | AxImportedDefinedness name' => Definedness.axiom name'
                                                         
      | AxPrev
          (* TODO make `and` bind tighter than `∃,` *)
        => (prev x == (∃, (b0 and (x ∈ ∘b0 ))))%ml
                                            
      | AxTrace
        => (∃,([[ Trace ]] == b0))%ml
                                         
      | AxTraceSuffix
        => ([[ TraceSuffix ]] == (μ, ([[ Trace ]] or (prev B0))))%ml

      | AxInf
        => ([[ TraceSuffix ]] ⊆ ∘ ([[ TraceSuffix ]]))%ml

      | AxNextOut
        => ((∘(¬([[ TraceSuffix ]]))) ⊆ (¬ [[ TraceSuffix ]]))%ml

      | AxNextPFun
        => (sym sym_next) : TraceSuffix ⇀ TraceSuffix

      | AxNextInj
        => patt_forall_of_sort TraceSuffix (patt_forall_of_sort TraceSuffix ( ( (∘b0 == ∘b1) and (¬ (∘b1 == ⊥))  ) ---> (b0 == b1)  ))

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

      Definition Mnext m := app_ext (sym_interp sym_next) (Singleton (Domain M) m).
      Definition Mnext_ext (A : Power (Domain M)) : Power (Domain M) :=
        fun (e : Domain M) => exists (m : Domain M), In (Domain M) A m /\ In (Domain M) (Mnext m) e.

      Definition Mprev m := app_ext (sym_interp sym_prev) (Singleton (Domain M) m).
      Definition Mprev_ext (A : Power (Domain M)) : Power (Domain M) :=
        fun (e : Domain M) => exists (m : Domain M), In (Domain M) A m /\ In (Domain M) (Mprev m) e.
      
      Lemma Mnext_Mprev_inversions : forall (m1 m2 : Domain M),
          In (Domain M) (Mnext m2) m1 <-> In (Domain M) (Mprev m1) m2.
      Proof.
        pose proof (Hprev := satisfies_theory_impl_satisfies_named_axiom M_satisfies_theory AxPrev).
        cbn in Hprev.
        unfold satisfies_model in Hprev.
        intros.
        remember ((fun x : evar_name => m1)) as evar_val.
        remember (fun X : svar_name => Empty_set (Domain M)) as svar_val.
        specialize (Hprev evar_val svar_val).
        apply equal_impl_interpr_same in Hprev. 2: auto.
        unfold Same_set in Hprev. unfold Included in Hprev. unfold In in Hprev.
        unfold prev in Hprev.
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
        2: { Unset Printing Implicit.
             unfold signature in *.
             autorewrite with ml_db. simpl.
             Search M_predicate T_predicate.
             admit. }
        (* TODO make `simpl` not simplify ands, ors etc to implications *)
        (* TODO make a hint database to solve M_predicate goals *)
        (* TODO solve M |= theory automatically *)
        rewrite -> pattern_interpretation_set_builder in Hprev. (* Blocked by evar_open *)


        
        destruct Hprev as [Hprev1 Hprev2].

        Search Same_set eq.
      Admitted.
      
    End basics.
      
    
  End LTL.

End LTL.
