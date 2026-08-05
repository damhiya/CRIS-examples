From CRIS.common Require Import CRIS.
From CRIS.mutsum Require Import MutFA MutGA.
From CRIS.mutsum Require Import MutHeader MutMainI MutMainA.
From CRIS.apc Require Import APCHeader APC APCA APCC APCTactics.

Set Implicit Arguments.

Module MutMainIA. Section MutMainIA.
  Import MutAUX.
  Context `{!crisG Γ Σ α β τ Hinv Hsub}.

  Context (Sp SpPure: specmap).
  Context (APCInSp : APCA.sp ⊆ Sp).
  Context (FInPure : MutFA.SpF ⊆ SpPure).
  Context (PureInSp : SpPure ⊆ Sp).

  Definition Ist (_ : stateGS Σ) : iProp Σ := True%I.

  Local Definition MutMainAMod := ((MutMainA.t true Sp) ★ APCA.t SpPure Sp).
  Local Definition MutMainIMod := ((MutMainI.t) ★ APCA.t SpPure Sp).
  Local Notation IstFull :=
    (λ STATE, (Ist STATE ∗ IstEq (APCA.t SpPure Sp) STATE)%I).
  
  (*************)

  Lemma simF_main:
    ⊢ ISim.sim_fun open MutMainAMod MutMainIMod IstFull entry.
  Proof using APCInSp FInPure PureInSp.
    cStartFunSim.

    (* SRC: precondition *)
    cStepsS. cSimpl.

    (* SRC: handle pure (APC) *)
    rewrite /MutMainI.mainF /MutMainA.main_body /pure.
    cForceS 11. cStepsS. cSimpl.
    cForcesS. iSplitR; eauto.
    
    (* SRC: inlining APC *)
    cInlineS. cStepsS. iDestruct "ASM" as "[-> <-]".
    cStepsS. rewrite /APC. cForceS 1. cStepsS.

    (* SRC, TGT: cCall mutg using APC tactic *)
    cStepsT. apcCall "IST" as (?) "ISTPOST"; eauto.
    { instantiate (1:=0). eapply OrdArith.lt_from_nat. nia. }
    { instantiate (1:=10). eapply OrdArith.lt_from_nat. nia. }
    { instantiate (1:=10). iSplit; eauto. 
      { iPureIntro. esplits; eauto; [unfold mut_max; nia|refl]. }
    }
    iDestruct "ISTPOST" as "[IST ->]".
    
    (* SRC: jump APC *)
    apcS. cStepsS. cStepsT. cStepsT.
    cForcesS. iSplitR; first done.
    cStepsS. cForcesS.

    (* SRC, TGT: prove the IST *)
    cStep. iSplitR "IST"; eauto.
    Unshelve. all: ss.
  (*SLOW*)Qed.

  Theorem sim:
    MutMainA.init_cond ⊢ ISim.t open MutMainAMod MutMainIMod IstFull.
  Proof.
    iIntros "C".
    iApply (ISim_reflR open (MutMainA.t true Sp) MutMainI.t
      (APCA.t SpPure Sp) Ist with "[C] []").
    - rewrite /ISim.init_ist. iIntros (WF). iSplit.
      { iPureIntro. mod_tac. }
      iIntros (STATE) "SRC TGT". done.
    - rewrite /ISim.sim_funs. iIntros (WF). iSplit.
      { iPureIntro. split; mod_tac. }
      iIntros (fn) "%Hfn".
      repeat rewrite Mod.dom_fnsems_add in Hfn.
      set_unfold in Hfn; des; subst.
      iApply simF_main.
  Qed.

  Theorem ctxr:
    ⊢ ctx_refines
        (MutMainI.t ★ APCA.t SpPure Sp)
        (MutMainA.t true Sp ★ APCA.t SpPure Sp).
  Proof.
    iApply (main_adequacy
      (MutMainI.t ★ APCA.t SpPure Sp)
      (MutMainA.t true Sp ★ APCA.t SpPure Sp)
      IstFull).
    iApply sim. done.
  Qed.

  Theorem ctxr_close:
    ⊢ ctx_refines
        (MutMainA.t true Sp ★ APCC.t Sp)
        (MutMainA.t false Sp ★ APCC.t Sp).
  Proof using APCInSp FInPure PureInSp.
    iApply (main_adequacy _ _
      (λ STATE, (True ∗ IstEq (APCC.t Sp) STATE)%I)).
    iApply (ISim_reflR open (MutMainA.t false Sp) (MutMainA.t true Sp)
      (APCC.t Sp) (λ _ : stateGS Σ, True%I)).
    - rewrite /ISim.init_ist. iIntros (WF). iSplit.
      { iPureIntro. mod_tac. }
      iIntros (STATE) "SRC TGT". done.
    - rewrite /ISim.sim_funs. iIntros (WF). iSplit.
      { iPureIntro. split.
        - mod_tac.
        - set_unfold; naive_solver.
      }
      iIntros (fn) "%Hfn".
      repeat rewrite Mod.dom_fnsems_add in Hfn.
      set_unfold in Hfn; des; subst.
      cStartFunSim.
      cStepsS. cForcesT.
      cSimpl. cStepsT.
      rewrite /MutMainA.main_body /pure /SModTr.trans_fnsem /SModTr.HoareFun. cStepsT.
      cSimpl. cStepsT. cInlineT. cForcesT.
      iDestruct "GRT" as "(% & %)". subst. cSimpl. iSplitR; et.
      cStepsT. cForcesT. iSplitR; et.
      cStepsT. cStepsS. cStep. iDestruct "IST" as "[_ IST]". iFrame; eauto.
  Unshelve. all: et.
  Qed.

End MutMainIA. End MutMainIA.
