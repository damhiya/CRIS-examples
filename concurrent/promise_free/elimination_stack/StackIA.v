From CRIS.common Require Import CRIS.
From CRIS.lib Require Import BiEnrichedProset.
From CRIS.scheduler Require Import SchHeader SchI SchA SchTactics.
From CRIS.promise_free.algebra Require Import HistoryRA AtomicRA.
From CRIS.promise_free.system
  Require Import SystemHeader SystemA SystemTactics.
From CRIS.promise_free.elimination_stack
  Require Import StackHeader StackA StackI.
From CRIS.promise_free.elimination_stack
  Require Import StackIANewStack StackIAPush StackIAPop.
From CRIS.helping Require Export HelpingTactics.

Module StackIM. Section StackIM.
  Context `{!crisG Γ Σ α β τ _S _I,
    _HIST : !histGS, _ATOMIC : !atomicG, _SYS : !sysGS,
    _STACK : !stackG, _HELP : !helpingGS, _SCH : !schGS}.

  Context (mn : string) (sp_user sp : specmap).

  Local Definition SysF := CFilter.filter (Helping.exports mn)
    (SystemA.t sp_user (↑stackN) sp).
  Local Definition SchF := CFilter.filter (Helping.exports mn) SchI.t.
  Local Definition MA :=
    ((StackM.t mn (SystemA.sp sp_user (↑stackN)) ★
        HelpingOn.t mn StackM.jobCode) ★ SysF) ★ SchF.
  Local Definition MI :=
    ((CFilter.filter (Helping.exports mn) StackI.t ★
        HelpingDummy.t mn) ★ SysF) ★ SchF.
  Local Definition StackHelpM :=
    StackM.t mn (SystemA.sp sp_user (↑stackN)) ★
      HelpingOn.t mn StackM.jobCode.
  Local Definition Ist (STATE : stateGS Σ) : iProp Σ :=
    (IstHelp (IstEq StackHelpM STATE) ⊤ ∗
      IstEq (SysF ★ SchF) STATE)%I.

  Lemma sim (Hsys : (SystemA.sp sp_user (↑stackN)) ⊆ sp) :
    hinv_ownE ⊤ ⊢ ISim.t open MA MI Ist.
  Proof.
    iIntros "HE".
    rewrite /MA /MI /Ist /StackHelpM.
    rewrite -(assoc Mod.add
      (StackM.t mn (SystemA.sp sp_user (↑stackN)) ★
        HelpingOn.t mn StackM.jobCode) SysF SchF).
    rewrite -(assoc Mod.add
      (CFilter.filter (Helping.exports mn) StackI.t ★
        HelpingDummy.t mn) SysF SchF).
    iApply (ISim_reflR open StackHelpM
      (CFilter.filter (Helping.exports mn) StackI.t ★
        HelpingDummy.t mn)
      (SysF ★ SchF) (fun STATE =>
        IstHelp (IstEq StackHelpM STATE) ⊤)).
    - mod_tac.
    - mod_tac.
    - intros _. mod_tac.
    - iIntros (STATE fn) "%Hfn".
      rewrite Mod.dom_fnsems_add in Hfn.
      unfold StackM.t, HelpingOn.t in Hfn.
      cbn in Hfn. set_unfold in Hfn; des; subst.
      + rewrite !assoc. iApply (new_stack_simF mn sp_user sp).
      + rewrite !assoc. iApply (push_simF mn sp_user sp).
      + rewrite !assoc. iApply (pop_simF mn sp_user sp).
      + cStartFunSim; cStepsT; ss.
      + cStartFunSim; cStepsT; ss.
    - iIntros (STATE) "SRC TGT".
      rewrite /IstHelp. iFrame "HE".
      iApply (state_eq_init_same with "SRC TGT").
  Qed.
End StackIM. End StackIM.

From CRIS.helping Require Export HelpingFacts.

Module StackIA. Section StackIA.
  Context `{!crisG Γ Σ α β τ _S _I,
    _HIST : !histGS, _ATOMIC : !atomicG, _SYS : !sysGS,
    _STACK : !stackG, _HELP : !helpingGS, _SCH : !schGS}.

  Local Lemma stack_atomic_fun_src `{STATE : !stateGS Σ} {X X2 : Type}
      (P : X → iProp Σ)
      (body : X → itree crisE (Any.t * X2))
      (Q : X → X2 → Any.t → iProp Σ)
      (fls flt : gmap fname (option fbody))
      (Ist : iProp Σ) (E1 E2 : coPset)
      g R_t RR ps pt (msk_s : emask) (sp_s : specmap) itt :
    (∀ x,
      P x -∗
      wsim fls flt Ist (E1 ∪ ↑stackN, E2 ∪ ↑stackN) g _ R_t
        (λ rets rett,
          o=> winv (E1 ∪ ↑stackN, E2 ∪ ↑stackN) ∗
            Q x rets.2 rets.1 ∗ RR rets.1 rett)
        true pt
        (⇓sbox(msk_s) (⇓smod(sp_s) (body x))) itt) -∗
    wsim fls flt Ist (E1, E2) g Any.t R_t RR ps pt
      (⇓sbox(msk_s) (⇓smod(sp_s) (stack_atomic_fun P body Q))) itt.
  Proof.
    iIntros "SIM". rewrite /stack_atomic_fun.
    cNormS. case_match; cStepsS; ss. case_match; cStepsS; ss.
    iPoseProof ("SIM" with "ASM") as "SIM".
    appendRetT. wbind _ "SIM" as ([ret_s x2_s] ret_t) ">[W [Q RR]]".
    cNormS; case_match; cStepsS; ss. iApply wsim_fold; iFrame.
    cForceS. iFrame. cStep; iFrame.
  Qed.

  Lemma ctxr (sp_user sp : specmap) :
    (SystemA.sp sp_user (↑stackN)) ⊆ sp →
    help_init_cond ⊢
      ctx_refines
        (StackI.t ★ SystemA.t sp_user (↑stackN) sp ★ SchI.t)
        (StackA.t (SystemA.sp sp_user (↑stackN)) ★
          SystemA.t sp_user (↑stackN) sp ★ SchI.t).
  Proof.
    intros Hsys.
    iIntros "H".
    iApply (helping_main
      (fun mn => StackM.t mn (SystemA.sp sp_user (↑stackN)))
      (StackA.t (SystemA.sp sp_user (↑stackN))) StackI.t
      (SystemA.t sp_user (↑stackN) sp)
      StackM.jobCode with "H").
    { iIntros (mn) "HE". rewrite !CFilter.filter_app.
      (* intermediate refinement with helping facilities *)
      rewrite comm assoc (comm _ (HelpingDummy.t mn)).
      jIntros (ctx_refines_BiProset) "((STACK & DUMMY) & SYS & SCH)".
      jPoseProof main_adequacy with "[HE]" "[STACK DUMMY SYS SCH]" as "M".
      { iApply (StackIM.sim mn sp_user sp); et. }
      { jFrame. }
      rewrite /StackIM.MA.
      jDestruct "M" as "[[[STACK HELP] SYS] SCH]".
      jFrame.
    }

    iIntros (mn). rewrite !CFilter.filter_app.
    jIntros (ctx_refines_BiProset)
      "(STACK & ((SYS & SCH) & HELP))".
    iAssert
      (ctx_refines
        ((StackM.t mn (SystemA.sp sp_user (↑stackN)) ★
            HelpingOff.t mn StackM.jobCode) ★
          CFilter.filter (Helping.exports mn)
            (SystemA.t sp_user (↑stackN) sp) ★
          CFilter.filter (Helping.exports mn) SchI.t)
        (StackA.t (SystemA.sp sp_user (↑stackN)) ★
          CFilter.filter (Helping.exports mn)
            (SystemA.t sp_user (↑stackN) sp) ★
          CFilter.filter (Helping.exports mn) SchI.t))%I
      as "REF".
    { iApply (main_adequacy _ _
        (fun STATE =>
          (state_init_tgt ({[mn]} : gset string) ∅ STATE ∗
           IstEq
             (CFilter.filter (Helping.exports mn)
                (SystemA.t sp_user (↑stackN) sp) ★
              CFilter.filter (Helping.exports mn) SchI.t) STATE)%I)).
    iStopProof.
    iIntros "_".
    iApply (ISim_reflR open
      (StackA.t (SystemA.sp sp_user (↑stackN)))
      (StackM.t mn (SystemA.sp sp_user (↑stackN)) ★
        HelpingOff.t mn StackM.jobCode)
      (CFilter.filter (Helping.exports mn)
          (SystemA.t sp_user (↑stackN) sp) ★
        CFilter.filter (Helping.exports mn) SchI.t)
      (fun STATE => state_init_tgt ({[mn]} : gset string) ∅ STATE)).
    - unfold StackA.t, StackM.t, HelpingOff.t; cbn.
      apply submseteq_nil_l.
    - mod_tac.
    - intros _. mod_tac.
    - iIntros (STATE fn) "%Hfn".
      unfold StackA.t in Hfn. cbn in Hfn.
      set_unfold in Hfn; des; subst.
    { (* new_stack *)
      cStartFunSim.
      rewrite /StackM.new_stack /StackA.new_stack.
      cStepS.
      cStepsT.
      iApply stack_atomic_fun_src.
      iIntros ([[tid stid] V]) "[-> TV]".
      cForceT (tid, stid, V).
      cForceT (tt↑). cForcesT.
      iFrame "TV". repeat iSplit; eauto.
      cStepsT.
      cNormS. cNormT.
      iApply wsim_bind_strong.
      iApply isim_wsim. iIntros "WINV".
      iApply (isim_mono _ _ _ _ _ _ _
        (fun x y : () => (winv (∅, ∅) ∗ ist_with_eq _ x y)%I)
        _ _ _).
      - iIntros (ret_s ret_t) "[WINV [-> IST]]". iFrame "WINV".
        sYields. sYieldS.
        iDestruct "GRT" as "[%EQ GRT]".
        subst _q0.
        cForceS (_q↑, tt).
        cForcesS.
        cStep. iFrame "GRT IST". auto.
      - iApply isim_frame. iSplitL "WINV"; first iFrame.
        iApply isim_refl.
        + intros; ss.
        + intros; ss.
        + iFrame "IST".
    }
    { (* push *)
      cStartFunSim.
      rewrite /StackM.push /StackA.push /stack_atomic_fun.
      cStepsS. cStepsT.
      destruct _q as [[[[value γs] tid] stid] V].
      iDestruct "ASM" as (stack) "[-> [#HANDLE TV]]".
      cForceT (value, γs, tid, stid, V).
      cForceT ((stack, value, γs)↑). cForcesT.
      iFrame "HANDLE TV". repeat iSplit; eauto.
      cStepsT.
      cNormS.
      iApply wsim_bind. iSplitL "IST".
      { iApply isim_wsim. iIntros "WINV". iApply isim_refl.
        - intros; ss.
        - intros; ss.
        - iFrame. }
      iIntros (??) "[-> IST]".
      cStepsT.
      cInlineT. cStepsT. rewrite /HelpingOff.run. cStepsT.
      aUnfoldS. aUnfoldT. sYields. sYieldS. cStepsS.
      rewrite /StackM.jobCode. cForcesT; iFrame.
      cStepsT. cForceS (inr _). cForcesS; iFrame.
      sYields. sYieldS. cStepsS.
      instantiate (1 := Val.zero↑).
      iDestruct "GRT" as "[-> GRT]".
      cForcesS. iFrame "GRT".
      cStep. iFrame. auto.
    }
    { (* pop *)
      cStartFunSim.
      rewrite /StackM.pop /StackA.pop /stack_atomic_fun.
      cStepsS. cStepsT.
      destruct _q as [[[γs tid] stid] V].
      cStepsS.
      iDestruct "ASM" as "[%stack [-> [#HANDLE TV]]]".
      cForceT (γs, tid, stid, V). cForcesT.
      iSplitL "TV".
      { iExists stack. iFrame "HANDLE TV". eauto. }
      aAddY. sYields. case_match.
      { cStepsT. cInlineT. cStepsT. rewrite /HelpingOff.help. cStepsT.
        sYields. sYieldS.
        aStep. iExists 0. iAuIntro.
        iAaccIntro "% $ !>" with "". iSplit; first eauto.
        iIntros "%ret_t $ !>"; iExists ret_t; iModIntro.
        iIntros "IST".
        cStepsT. sYieldS. cForcesS; iFrame "GRT".
        cStep. iFrame. auto.
      }
      cStepsT. sYieldS. aStep.
      iExists 0. iAuIntro.
      iAaccIntro "% $ !>" with "". iSplit; first eauto.
      iIntros "%ret_t $ !>"; iExists ret_t; iModIntro.
      iIntros "IST".
      cStepsT. sYieldS. cForcesS; iFrame "GRT".
      cStep. iFrame. auto.
    }
    - iIntros (STATE) "SRC TGT".
      assert (Hscopes :
        list_to_set
          (Mod.scopes
            (StackM.t mn (SystemA.sp sp_user (↑stackN)) ★
              HelpingOff.t mn StackM.jobCode)) =
        ({[mn]} : gset string)).
      { apply set_eq. intros scope.
        unfold Mod.add; cbn.
        unfold StackM.t, HelpingOff.t; cbn. set_solver. }
      assert (Hinit :
        Mod.initial_st
          (StackM.t mn (SystemA.sp sp_user (↑stackN)) ★
            HelpingOff.t mn StackM.jobCode) = ∅).
      { unfold Mod.add, StackM.t, HelpingOff.t; cbn.
        apply map_eq. intros key. rewrite lookup_union_with.
        simpl_map. reflexivity. }
      iEval (rewrite Hscopes Hinit) in "TGT".
      iExact "TGT".
    }
    jApply "REF".
    jFrame "STACK HELP SYS SCH".
  Qed.
End StackIA. End StackIA.
