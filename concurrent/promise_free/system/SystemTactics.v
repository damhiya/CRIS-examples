From CRIS.common Require Import CRIS.
From CRIS.promise_free.system Require Import SystemHeader SystemA.

Section wsim.
  Context `{!crisG Γ Σ α β τ _S _I, _SYS: !sysGS}.
  Context `{STGS : !stateGS Σ}.

  Lemma wsim_system_yield_ir
      fl_src fl_tgt Ist g R_src R_tgt RR p_src p_tgt
      itr_src itr_tgt
      (tid : Ident.t) (stid : nat) (V : TView.t)
      (E : coPset)
      (msk_src msk_tgt : emask)
      sp_src sp_tgt :
    sp_src.1 !! fid SystemHdr.yield = fsp_some (SystemA.yield_spec E) →
    sp_tgt.1 !! fid SystemHdr.yield = None →
    (∀ X, msk_tgt _ (subevent _ (Choose X))) →
    (msk_tgt _ (subevent _ (Call SystemHdr.yield.1 ()↑))) →
    Ist ∗
    (tview_sys tid stid V) ∗
    (Ist -∗
      (tview_sys tid stid V) -∗
      wsim fl_src fl_tgt Ist (E, E) g R_src R_tgt RR true true
        (SB.sandbox msk_src (SModTr.trans sp_src 𝒴) >>= itr_src)
        (itr_tgt ())) ⊢
    wsim fl_src fl_tgt Ist (E, E) g R_src R_tgt RR p_src p_tgt
      (SB.sandbox msk_src (SModTr.trans sp_src 𝒴) >>= itr_src)
      (SB.sandbox msk_tgt (SModTr.trans sp_tgt 𝒴) >>= itr_tgt).
  Proof.
    intros Hsps Hspt Hmsk Hcall. iIntros "?".
    rewrite /System.yield; unseal "System".
    cCoind CIH g' Hgg' with p_src p_tgt. iIntros "[IST [TV KTR]] /=".
    rewrite {2 3}unfold_iterC.

    cStepsS. des_if; cStepS; ss.
    cStepsT. rewrite Hmsk. cStepsT. destruct _q as [[|]|]; cycle 2.
    { cStepsT.
      cForceS (Some false). cStepsS.
      iApply wsim_mono_knowledge; cycle 1.
      { iApply ("KTR" with "IST TV"). }
      { ii; iIntros "G"; iPoseProof (Hgg' with "G") as "$"; done. }
    }
    { cStepsT. rewrite Hspt. cStepsT. rewrite Hcall. cStepsT.
      cForceS (Some true). cStepsS. rewrite Hsps /=.
      cStepS. des_if; cStepS; ss. cForceS (tid, stid, V).
      cStepS. des_if; cStepS; ss. cForceS.
      cStepS. des_if; cStepS; ss. cForceS.
      iFrame "TV". iSplit; eauto.
      cStepS. des_if; cStepS; ss.
      cCall "IST" as (ret) "IST".
      cStepS. des_if; cStepS; ss.
      cStepS. des_if; cStepsS; ss. iDestruct "ASM" as "[-> [-> V]]".
      cStepsS. cStepsT. cByCoind CIH. iFrame.
    }
    cForceS (Some false). cStepsS. cStepsT.
    cByCoind CIH. iFrame.
  (*SLOW*)Qed.

  Lemma wsim_system_yield_src
      fl_src fl_tgt Ist g R_src R_tgt RR p_src p_tgt
      itr_src itr_tgt
      (E : coPset)
      (msk_src : emask)
      sp_src :
    wsim fl_src fl_tgt Ist (E, E) g R_src R_tgt RR true p_tgt
      (itr_src ())
      itr_tgt ⊢
    wsim fl_src fl_tgt Ist (E, E) g R_src R_tgt RR p_src p_tgt
      (SB.sandbox msk_src (SModTr.trans sp_src 𝒴) >>= itr_src)
      itr_tgt.
  Proof.
    iIntros "S"; rewrite /System.yield; unseal "System".
    rewrite unfold_iterC; cStepsS.
    des_if; cStepsS; ss. cForceS (None); cStepsS; done.
  Qed.
End wsim.
