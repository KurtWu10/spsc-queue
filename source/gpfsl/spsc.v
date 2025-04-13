From gpfsl.logic Require Import atomics new_delete proofmode repeat_loop view_invariants.
From gpfsl.examples Require Import uniq_token.

(** Single-producer single-consumer queue, based on gpfsl-examples/mp *)

(* "memory layout" of a queue *)
Notation tail := 0 (only parsing).
Notation head := 1 (only parsing).
Notation buffers := 2 (only parsing).

Section code.
  Notation capacity := 1 (only parsing).

  Definition enqueue (queue buffer : expr) : expr :=
    let: "tail_val" := !ʳˡˣ(queue +ₗ #tail) in
    let: "head_val" := !ᵃᶜ(queue +ₗ #head) in
    if:
      "tail_val" - "head_val" = #capacity
    then
      #-1
    else
      queue +ₗ (#buffers + ("tail_val" `mod` #capacity)) <- buffer ;;
      queue +ₗ #tail <-ʳᵉˡ "tail_val" + #1.

  Definition dequeue (queue : expr) : expr :=
    let: "head_val" := !ʳˡˣ(queue +ₗ #head) in
    let: "tail_val" := !ᵃᶜ(queue +ₗ #tail) in
    if:
      "tail_val" - "head_val" = #0
    then
      #-1
    else
      let: "buffer" := !(queue +ₗ (#buffers + ("head_val" `mod` #capacity))) in
      queue +ₗ #head <-ʳᵉˡ "head_val" + #1 ;;
      "buffer".

  Definition program : expr :=
    let: "queue" := new [ #2 + #capacity ] in
    "queue" +ₗ #tail <- #0 ;;
    "queue" +ₗ #head <- #0 ;;
    "queue" +ₗ #buffers <- #0 ;;
    Fork (
      enqueue "queue" #42
    ) ;;
    dequeue "queue".
End code.

Section inv.
  (* using implicit generalisation for history, atomics and unique token, respectively *)
  Context `{!noprolG Σ, !atomicG Σ, !uniqTokG Σ}.

  (*
  Reordered from Definition 12.2, invariant for mp

  the two choices of the outer '∨' (with ⌜h = {[t0 := (#0, V0)]}⌝)
  signals that there are two variants inside the invariant

  the invariant represents information related to a single-write atomic with history h under V
  in the first variant, h = {[t0 := (#0, V0)]}, and there is no information on V
  in the second variant, h is extended with a new message,
    and either we have a unique token, or we have the data

  for the producer,
    it only cares about the single-writer ownership (with arbitrary h),
    and can easily establish the invariant after the release write

  for the consumer,
    it requires information of the history h,
    so it exam all possible paths of ∨ and react appropriately

  the complexity of adding read to the producer is that it needs to handle the second branch of ∨,
  i.e. we need a way to prevent the producer from reading the updated value 1
  to do this, we add another unique token to the first branch of ∨ with separation conjunction,
  and also pass the new unique token to the producer
  in this case, the producer is prevented from having the second branch
  *)
  Definition spsc_inv_def (l : loc) (Tok1 Tok2 : gname) (γl0 γl2 : view_inv_pool_name) : vProp Σ := (
    ∃ (Vl0 Vl2 : view) (hl0 hl2 : absHist) (t0 t1 : time) (V0 V1 : view),
      @{Vl0}(l sw↦{γl0} hl0) ∗ ((
        ⌜hl0 = {[t0 := (#0, V0)]}⌝
      ) ∨ (
        UTok Tok2 ∗ ∃ (t2 : time) (V2 : view), ⌜
          (t0 < t2)%positive ∧ 
          hl0 = {[t2 := (#1, V2); t0 := (#0, V0)]}
        ⌝ ∗ (
          UTok Tok1 ∨
          @{V2}((l >> Z.to_nat buffers) ↦ #42)
        )
      )) ∗
      @{Vl2} ((l >> Z.to_nat head) sw↦{γl2} hl2) ∗ ((
        ⌜hl2 = {[t1 := (#0, V1)]}⌝
      ) ∨ (
        ∃ (t3 : time) (V3 : view), ⌜
          hl2 = {[t3 := (#1, V3); t1 := (#0, V1)]}
        ⌝
      )) ∗ (⌜hl0 = {[t0 := (#0, V0)]} → hl2 = {[t1 := (#0, V1)]}⌝)
  )%I.

  Definition spsc_inv_aux : seal spsc_inv_def.
  Proof. by eexists. Qed.

  Definition spsc_inv := unseal spsc_inv_aux.
  Definition spsc_inv_eq : (spsc_inv = spsc_inv_def) := seal_eq spsc_inv_aux.

  #[global]
  Instance spsc_inv_objective (l : loc) (Tok1 Tok2 : gname) (γl0 γl2 : view_inv_pool_name) : Objective (spsc_inv l Tok1 γl0 Tok2 γl2).
  Proof.
    rewrite spsc_inv_eq.
    unfold spsc_inv_def.
    apply exists_objective => Vl0.
    apply exists_objective => Vl2.
    apply exists_objective => hl0.
    apply exists_objective => hl2.
    apply exists_objective => t0.
    apply exists_objective => t1.
    apply exists_objective => V0.
    apply exists_objective => V1.
    apply sep_objective.
    {
      apply view_at_objective.
    }
    apply sep_objective.
    {
      apply or_objective.
      apply pure_objective.
      {
        apply sep_objective.
        {
          apply UTok_objective.
        }
        apply exists_objective => t2.
        apply exists_objective => V2.
        apply sep_objective.
        {
          apply pure_objective.
        }
        apply or_objective.
        {
          apply UTok_objective.
        }
        apply view_at_objective.
      }
    }
    apply sep_objective.
    {
      apply view_at_objective.
    }
    apply sep_objective.
    {
      apply or_objective.
      {
        apply pure_objective.
      }
      apply exists_objective => t3.
      apply exists_objective => V3.
      apply pure_objective.
    }
    apply pure_objective.
  Qed.
End inv.

Section proof.
  Context `{!noprolG Σ, !atomicG Σ, !uniqTokG Σ}.

  Definition mpN (n: loc) : namespace := nroot .@ "mpN" .@ n.

  Lemma spsc_establish_invariant :
    ∀ (l : loc) (Tok1 Tok2 : gname) (γl0 γl2 : view_inv_pool_name) (t0 t1 : time) (V0 V1 Vl0 Vl2 : view) (E : coPset),
      @{Vl0} l sw↦{γl0} {[t0 := (#0, V0)]} ∗
      @{Vl2} (l >> Z.to_nat head) sw↦{γl2} {[t1 := (#0, V1)]} ={E}=∗
        inv (mpN l) (spsc_inv l Tok1 Tok2 γl0 γl2).
  Proof.
    intros.
    iIntros "(v_at0 & v_at2)".
    iMod (inv_alloc (mpN l) _ (spsc_inv l Tok1 Tok2 γl0 γl2) with "[v_at0 v_at2]") as "#invariant".
    {
      iNext.
      iEval (rewrite spsc_inv_eq).
      iUnfold spsc_inv_def.
      iExists Vl0, Vl2, {[t0 := (#0, V0)]}, {[t1 := (#0, V1)]}, t0, t1, V0, V1.
      iSplitL "v_at0";
        [ iExact "v_at0" | ].
      iSplitL "".
      {
        iLeft.
        iPureIntro.
        reflexivity.
      }
      iSplitL "v_at2";
        [ iExact "v_at2" | ].
      iSplitL "".
      {
        iLeft.
        iPureIntro.
        reflexivity.
      }
      iPureIntro.
      intros.
      reflexivity.
    }
    iApply "invariant".
  Qed.

  Lemma spsc_producer :
    ∀ (tid : thread_id) (l : loc) (Tok1 Tok2 : gname) (γl0 γl2 : view_inv_pool_name) (t0 t1 : time) (V0 V1 : view),
    {{{
      inv (mpN l) (spsc_inv l Tok1 Tok2 γl0 γl2) ∗
      l sw⊒{γl0} {[t0 := (#0, V0)]} ∗
      (l >> Z.to_nat buffers) ↦ ? ∗
      ((l >> Z.to_nat head) sy⊒{γl2} {[t1 := (#0, V1)]}) ∗
      UTok Tok2
    }}}
      enqueue #l #42 @ tid; ⊤
    {{{ RET #☠; True }}}.
  Proof.
    intros.
    iIntros "(#invariant & sw0 & na1 & sy2 & ⋄2) post".
    iPoseProof (AtomicSWriter_AtomicSync with "sw0") as "#sy0".
    iPoseProof (AtomicSync_lookup _ _ _ t0 with "sy0") as "#V0".
    {
      rewrite lookup_singleton.
      reflexivity.
    }
    iPoseProof (AtomicSync_AtomicSeen with "sy2") as "#sn2".
    iPoseProof (AtomicSync_lookup _ _ _ t1 with "sy2") as "#V1".
    {
      rewrite lookup_singleton.
      reflexivity.
    }

    unfold enqueue.

    (* [1] let: "tail_val" := !ʳˡˣ(l +ₗ #tail) in *)
    wp_op.
    iEval (rewrite shift_lblock_0).
    wp_bind (!ʳˡˣ_)%E.

    iInv "invariant" as "H" "Hclose".
    iEval (rewrite spsc_inv_eq) in "H".
    iUnfold spsc_inv_def in "H".
    iDestruct "H" as (Vl0_H Vl2_H hl0_H hl2_H t0_H t1_H V0_H V1_H) ">[v_at0 loaded_resource]".
    iDestruct (AtomicPtsTo_AtomicSWriter_agree_1 with "v_at0 [$sw0]") as "->".
    wp_apply (AtomicSWriter_read with "[$v_at0 $sw0 $V0]");
      [done | solve_ndisj | ..].
    iIntros (t v V V0_1) "((%h0 & _ & _) & _ & sw0 & v_at0)".
    iDestruct "loaded_resource" as "([%loaded_resource | loaded_resource] & unused)"; first last.
    {
      iExFalso.
      iDestruct "loaded_resource" as "[⋄2' _]".
      iApply (UTok_unique with "[$⋄2] [$⋄2']").
    }

    destruct (decide (t = t0)) as [-> | t_neq_t0]; first last.
    {
      iExFalso.
      rewrite lookup_insert_ne in h0.
      {
        done.
      }
      symmetry.
      apply t_neq_t0.
    }

    rewrite lookup_insert in h0.
    inversion h0.
    iMod ("Hclose" with "[v_at0 unused]") as "_".
    {
      iNext.
      iEval (rewrite spsc_inv_eq).
      iUnfold spsc_inv_def.
      iExists (Vl0_H ⊔ V0_1), _, {[t0 := (#0, V)]}, _, t0, _, V, _.
      assert (t0 = t0_H ∧ V0 = V0_H) as [-> ->].
      {
        destruct (decide (t0 = t0_H ∧ V0 = V0_H)) as [[-> ->] | _].
        {
          done.
        }
        rewrite map_eq_iff in loaded_resource.
        specialize (loaded_resource t0).
        rewrite lookup_singleton in loaded_resource.
        symmetry in loaded_resource.
        rewrite lookup_singleton_Some in loaded_resource.
        inversion loaded_resource as [t0_eq V0_eq].
        inversion V0_eq.
        split; done.
      }
      rewrite H1.
      iFrame "unused".
      iSplitL "v_at0";
        [iExact "v_at0" | ].
      iLeft.
      iPureIntro.
      reflexivity.
    }
    clear.
    iModIntro.
    wp_let.

    (* [2] let: "head_val" := !ᵃᶜ(l +ₗ #head) in *)
    wp_op.
    wp_bind (!ᵃᶜ _)%E.
    iInv "invariant" as "H" "Hclose".

    iEval (rewrite spsc_inv_eq) in "H".
    iUnfold spsc_inv_def in "H".
    iDestruct "H" as (V_ V4' h h_head t0' t0_head' V0' V0_head') ">[v_at0 [v_at0_props [v_at2 [v_at2_props %constraint]]]]".

    wp_apply (AtomicSeen_acquire_read with "[$sn2 $v_at2 $V1]");
      [solve_ndisj | ..].
    iIntros (t v VVV V' h') "(
      ((_ & %h'_leq_h) & %h'_t & _ & _) & 
      _ & _ & v_at2
    )".

    iDestruct (AtomicPtsTo_AtomicSWriter_agree_1 with "v_at0 [$sw0]") as "->".
    iDestruct "v_at0_props" as "[%v_at0_props | [⋄2' _]]"; last first.
    {
      iExFalso.
      iApply (UTok_unique with "[$⋄2] [$⋄2']").
    }
    assert (h_head = {[t0_head' := (#0, V0_head')]}) as ->.
    {
      apply constraint.
      apply v_at0_props.
    }
    apply (lookup_weaken _ _ _ _ h'_t) in h'_leq_h.
    apply lookup_singleton_Some in h'_leq_h as [-> v_props].
    inversion v_props.
    iMod ("Hclose" with "[v_at0 v_at2 v_at2_props]") as "_".
    {
      iNext.
      iEval (rewrite spsc_inv_eq).
      iUnfold spsc_inv_def.
      iExists _, _, _, _, _, _, _, _.
      iFrame "v_at0 v_at2 v_at2_props".
      iSplitR "".
      {
        iLeft.
        iPureIntro.
        reflexivity.
      }
      iPureIntro.
      intro unused.
      reflexivity.
    }
    clear.
    iModIntro.
    wp_let.

    (* [3] if: "tail_val" - "head_val" = #capacity *)
    wp_op.
    wp_op.
    wp_if.

    (* [4] l +ₗ (#buffers + ("tail_val" `mod` #capacity)) <- #42 *)
    wp_op.
    wp_op.
    wp_op.
    wp_write.

    (* [5] l +ₗ #tail <-ʳᵉˡ "tail_val" + #1 *)
    wp_op.
    iEval (rewrite shift_lblock_0).
    wp_op.
    iInv "invariant" as "H" "Hclose".
    iEval (rewrite spsc_inv_eq) in "H".
    iUnfold spsc_inv_def in "H".
    iDestruct "H" as (Vl0_H Vl2_H hl0_H hl2_H t0_H t1_H V0_H V1_H) ">[v_at0 (_ & unused)]"; clear.
    iDestruct (AtomicPtsTo_AtomicSWriter_agree_1 with "v_at0 [$sw0]") as "->".

    wp_apply (
      AtomicSWriter_release_write _ _ _ _ _ _ #1 ((l >> Z.to_nat buffers) ↦ #42)
      with "[$sw0 $v_at0 $na1 $V0]"
    );
      [solve_ndisj | ..].
    iIntros (t2 V2) "((%t1T & _) & _ & [v_na1 _] & v_at0)".

    iMod ("Hclose" with "[v_at0 v_na1 ⋄2 unused]");
      [| iModIntro; iApply "post"; done].
    iNext.
    iEval (rewrite spsc_inv_eq).
    iUnfold spsc_inv_def.
    iExists (Vl0_H ⊔ V2), _, {[t2 := (#1, V2); t0 := (#0, V)]}, _, t0, _, V, _.
    iDestruct "unused" as "(v_at2 & v_at2_props & unused)".
    iFrame "v_at2".
    iFrame "v_at2_props".
    iFrame "v_at0".
    iSplitR "".
    {
      iRight.
      iSplitL "⋄2";
        [iExact "⋄2" | ].
      iExists t2, V2.
      iSplitR;
        [| iRight; iExact "v_na1"].

      iPureIntro.
      split;
        [| reflexivity].

      unfold fresh_max_time in t1T.
      apply t1T.
      rewrite lookup_insert.
      unfold is_Some.
      eexists.
      reflexivity.
    }
    iPureIntro.
    intro wrong.
    exfalso.
    rewrite map_eq_iff in wrong.
    specialize (wrong t2).
    rewrite lookup_insert in wrong.
    symmetry in wrong.
    rewrite lookup_singleton_Some in wrong.
    destruct wrong as [wrong _].
    unfold fresh_max_time in t1T.
    specialize (t1T t0).
    rewrite lookup_insert in t1T.
    unfold is_Some in t1T.
    assert (∃ x : val * view, Some (#0, V) = Some x) as H.
    {
      eexists.
      reflexivity.
    }
    specialize (t1T H).
    rewrite wrong in t1T.
    lia.
  Qed.

  Lemma spsc_consumer :
    ∀ (tid : thread_id) (l : loc) (Tok1 Tok2 : gname) (γl0 γl2 : view_inv_pool_name) (t0 t1 : time) (V0 V1 : view),
    {{{
      inv (mpN l) (spsc_inv l Tok1 Tok2 γl0 γl2) ∗
      l sy⊒{γl0} {[t0 := (#0, V0)]} ∗ 
      ((l >> Z.to_nat head) sw⊒{γl2} {[t1 := (#0, V1)]}) ∗
      UTok Tok1
    }}}
      dequeue #l @ tid; ⊤
    {{{ v, RET #v; ⌜v = -1 ∨ v = 42⌝ }}}.
  Proof.
    intros.
    iIntros "(#invariant & #sy0 & sw2 & ⋄) post";
      set N := mpN l.
    iPoseProof (AtomicSync_lookup _ _ _ t0 with "sy0") as "#V0".
    {
      rewrite lookup_singleton.
      reflexivity.
    }
    iPoseProof (AtomicSync_AtomicSeen with "sy0") as "#sn0".

    unfold dequeue.

    (* [1] let: "head_val" := !ʳˡˣ(l +ₗ #head) in *)
    wp_op.
    wp_bind (!ʳˡˣ _)%E.
    iInv "invariant" as "H" "Hclose".
    iEval (rewrite spsc_inv_eq) in "H".
    iUnfold spsc_inv_def in "H".
    iDestruct "H" as (V'' V4'' h'' h_head' t0'' t0_head'' V0'' V0_head'') ">(v_at0 & v_at0_props & v_at2 & v_at2_props)".
    iDestruct (AtomicPtsTo_AtomicSWriter_agree_1 with "v_at2 [$sw2]") as "->".
    wp_apply (AtomicSWriter_read with "[$v_at2 $sw2 $V0]");
      [done | solve_ndisj | .. ].
    iIntros (t5 v5 V5 V6) "((%temp11 & _ & %temp12) & #V6 & sw2 & v_at2)".
    destruct (decide (t5 = t1)) as [-> | t5_neq_t0_head]; last first.
    {
      exfalso.
      rewrite lookup_insert_ne in temp11;
        [done | symmetry; exact t5_neq_t0_head].
    }
    rewrite lookup_insert in temp11.
    inversion temp11.
    iMod ("Hclose" with "[v_at0 v_at0_props v_at2 v_at2_props]") as "_".
    {
      iNext.
      iEval (rewrite spsc_inv_eq).
      iUnfold spsc_inv_def.
      iExists _, _, _, _, _, _, _, _.
      iFrame "v_at0 v_at0_props v_at2 v_at2_props".
    }
    clear.
    iModIntro.
    wp_let.

    (* [2] let: "tail_val" := !ᵃᶜ(l +ₗ #tail) in *)
    wp_op.
    iEval (rewrite shift_lblock_0).

    wp_bind (!ᵃᶜ _)%E.
    iInv "invariant" as "H" "Hclose".

    iEval (rewrite spsc_inv_eq) in "H".
    iUnfold spsc_inv_def in "H".
    iDestruct "H" as (V V4' h h_head t0' t0_head' V0' V0_head') ">[v_at0 loaded_resource]".

    wp_apply (AtomicSeen_acquire_read with "[$sn0 $v_at0 $V0]");
      [solve_ndisj | ..].
    iIntros (t v VVV V' h') "(
      ((_ & %h'_leq_h) & %h'_t & _ & %V0_and_V_leq_V') & 
      #V' & #sn0_new & v_at0
    )".

    destruct (decide (t = t0')) as [-> | t_neq_t0'].
    {
      iAssert (⌜v = #0⌝)%I as "->".
      {
        iDestruct "loaded_resource" as "([loaded_resource | loaded_resource] & _)".
        {
          iDestruct "loaded_resource" as "->".
          apply (lookup_weaken _ _ _ _ h'_t) in h'_leq_h.
          rewrite lookup_insert in h'_leq_h.
          inversion h'_leq_h.
          iPureIntro.
          reflexivity.
        }

        iDestruct "loaded_resource" as "[_ loaded_resource]".
        iDestruct "loaded_resource" as (t1_ V1_) "[[%t0'_lt_t1 ->] _]".

        iPureIntro.
        apply (lookup_weaken _ _ _ _ h'_t) in h'_leq_h.
        rewrite lookup_insert_ne in h'_leq_h.
        {
          rewrite lookup_insert in h'_leq_h.
          inversion h'_leq_h.
          reflexivity.
        }
        lia.
      }

      iMod ("Hclose" with "[loaded_resource v_at0]") as "_".
      {
        iNext.
        iEval (rewrite spsc_inv_eq).
        iUnfold spsc_inv_def.
        iExists (V ⊔ V'), _, h, _, t0', _, V0', _.
        iFrame "v_at0 loaded_resource".
      }
      clear.
      iModIntro.
      wp_let.

      (* [3] if: "tail_val" - "head_val" = #0 *)
      wp_op.
      wp_op.
      wp_if.

      iApply "post".
      iPureIntro.
      left.
      reflexivity.
    }

    iDestruct "loaded_resource" as "([loaded_resource | loaded_resource] & v_at2_resource)".
    {
      iDestruct "loaded_resource" as "->".
      exfalso.
      apply (lookup_weaken _ _ _ _ h'_t) in h'_leq_h.
      apply lookup_singleton_Some in h'_leq_h as [-> _].
      apply t_neq_t0'.
      reflexivity.
    }

    iDestruct "loaded_resource" as "[⋄2 loaded_resource]".
    iDestruct "loaded_resource" as (t1_ V1_) "[[%t0'_leq_t1 ->] resource]".

    apply (lookup_weaken _ _ _ _ h'_t) in h'_leq_h.
    assert (t = t1_) as ->.
    {
      destruct (decide (t = t1_)) as [t_eq_t1 | t_neq_t1];
        [exact t_eq_t1 |].

      exfalso.

      rewrite lookup_insert_ne in h'_leq_h;
        [| symmetry; exact t_neq_t1].
      rewrite lookup_insert_ne in h'_leq_h;
        [done | symmetry; exact t_neq_t0'].
    }
    rewrite lookup_insert in h'_leq_h.
    inversion h'_leq_h; subst v VVV; clear h'_leq_h.

    iDestruct "resource" as "[⋄' | v_na1]".
    {
      iExFalso.
      iApply (UTok_unique Tok1 with "⋄ ⋄'").
    }

    iDestruct (view_at_elim V1_ _ with "[V'] [$v_na1]") as "na1".
    {
      iApply (monPred_in_mono _ _ with "V'").
      simpl.
      transitivity (V0 ⊔ V1_);
        [exact (lat_join_sqsubseteq_r V0 V1_) | exact V0_and_V_leq_V'].
    }

    iMod ("Hclose" with "[v_at0 ⋄ ⋄2 v_at2_resource]") as "_".
    {
      iNext.
      iEval (rewrite spsc_inv_eq).
      iUnfold spsc_inv_def.

      iExists (V ⊔ V'), _, {[t1_ := (#1, V1_); t0' := (#0, V0')]}, _, t0', _, V0', _.

      iFrame "v_at2_resource".
      iFrame "v_at0".
      iRight.
      iSplitL "⋄2";
        [iExact "⋄2" | ].
      iExists t1_, V1_.
      iSplitL "";
        [iPureIntro; split; [exact t0'_leq_t1 | reflexivity]|].
      iLeft.
      iExact "⋄".
    }
    clear - h'_t.
    iModIntro.
    wp_let.

    (* [3] if: "tail_val" - "head_val" = #0 *)
    wp_op.
    wp_op.
    wp_if.

    (* [4] let: "ret" := !(l +ₗ (#buffers + ("head_val" `mod` #capacity))) in in *)
    wp_op.
    wp_op.
    wp_op.
    wp_read.
    wp_let.

    (* [5] l +ₗ #head <-ʳᵉˡ "head_val" + #1 *)
    wp_op.
    wp_op.
    wp_bind (_ <-ʳᵉˡ _)%E.
    iInv "invariant" as "H" "Hclose".
    iEval (rewrite spsc_inv_eq) in "H".
    iUnfold spsc_inv_def in "H".
    iDestruct "H" as (V'''' V4'''' h'''' h_head''' t0'''' t0_head'''' V0'''' V0_head'''') ">(v_at0 & v_at0_props & v_at2 & v_at2_props & asdf)".
    iDestruct (AtomicPtsTo_AtomicSWriter_agree_1 with "v_at2 [$sw2]") as "->".
    (* ⊒V0 here is release arbitrarily, otherwise there is an unknown shelved goal *)
    wp_apply (AtomicSWriter_release_write _ _ _ _ _ _ #1 (⊒V0) with "[$v_at2 $sw2 $V0]");
      [solve_ndisj | ].
    iIntros (t9 V9) "((%temp31 & %temp32 & %temp33) & #V9 & _ & v_at2)".
    iDestruct (AtomicPtsTo_AtomicSeen_latest with "[$v_at0] [$sn0_new]") as "%asdfg".
    iMod ("Hclose" with "[v_at0 v_at0_props v_at2 v_at2_props asdf]") as "_".
    {
      iNext.
      iEval (rewrite spsc_inv_eq).
      iUnfold spsc_inv_def.
      iExists V'''', (V4'''' ⊔ V9), h'''', {[t9 := (#1, V9); t1 := (#0, V5)]}, t0'''', t1, V0'''', V5.
      iFrame "v_at0 v_at2 v_at0_props".
      iSplitR "asdf".
      {
        iRight.
        iExists t9, V9.
        iPureIntro.
        reflexivity.
      }
      iPureIntro.
      intro impossible.
      exfalso.
      assert (h'''' !! t1_ = Some (#1, V1_)) as temp7.
      {
        apply (lookup_weaken h' h'''' t1_ (#1, V1_) h'_t asdfg).
      }
      assert (t0'''' = t1_ ∧ (#0, V0'''') = (#1, V1_)) as wrong.
      {
        rewrite <- (lookup_singleton_Some t0'''' t1_ (#0, V0'''') (#1, V1_)).
        rewrite impossible in temp7.
        apply temp7.
      }
      destruct wrong as [_ wrong].
      inversion wrong.
    }
    clear.
    iModIntro.
    wp_seq.

    iApply "post".

    iPureIntro.
    right.
    reflexivity.
  Qed.

  Lemma spsc_instance_gen_inv :
    ∀ (tid : thread_id),
    {{{ True }}}
      program @ tid; ⊤
    {{{ v, RET #v; ⌜v = -1 ∨ v = 42⌝ }}}.
  Proof.
    iIntros (thread1 Φ) "_ post".

    unfold program.
    unfold enqueue.
    unfold dequeue.

    wp_op.
    wp_apply wp_new;
      [done.. |].
    iIntros (l) "([_ | %impossible] & nas & _)";
      [| discriminate impossible].
    repeat iEval (rewrite own_loc_na_vec_cons) in "nas".
    repeat iEval (rewrite shift_lblock_assoc; simpl) in "nas".
    iDestruct "nas" as "(na0 & na1 & na2 & _)".

    wp_let.

    wp_op; iEval (rewrite shift_lblock_0); wp_write;
      repeat (wp_op; wp_write).

    iMod UTok_alloc as (Tok1) "⋄1".
    iMod UTok_alloc as (Tok2) "⋄2".

    iMod (AtomicPtsTo_from_na with "na0") as (γl0 t0 V0) "(#V0 & sw0 & at0)".
    iPoseProof (AtomicSWriter_AtomicSync with "sw0") as "#sy0".
    iDestruct (view_at_intro with "at0") as (Vl0) "(_ & v_at0)".

    iMod (AtomicPtsTo_from_na with "na1") as (γl1 t1 V1) "(#V1 & sw1 & at1)".
    iDestruct (view_at_intro with "at1") as (Vl1) "(_ & v_at1)".
    iPoseProof (AtomicSWriter_AtomicSync with "sw1") as "#sy1".

    iMod (spsc_establish_invariant l Tok1 Tok2 γl0 γl1 with "[$v_at0 $v_at1]") as "#invariant".

    wp_apply (wp_fork with "[sw0 na2 ⋄2]");
      [done | .. ].
    {
      iNext.
      iIntros (thread2).

      iDestruct (own_loc_na_own_loc with "na2") as "na2".
      wp_apply (spsc_producer with "[$invariant $sw0 $na2 $sy1 $⋄2]").
      iIntros "_".
      done.
    }

    iIntros "_".

    wp_seq.

    wp_apply (spsc_consumer thread1 l Tok1 Tok2 γl0 γl1 t0 t1 V0 V1 with "[$invariant $sy0 $sw1 $⋄1]").
    iApply "post".
  Qed.
End proof.
