From CRIS.common Require Import CRIS.
From CRIS.imp_system.mem Require Import MemA MemTactics.
From CRIS.celliostk Require Import CellioHeader CellioA CellioI.

Local Open Scope nat_scope.

Module CellioIA. Section CellioIA.
  Import CellioA.
  Context `{!crisG Γ Σ α β τ _S _I}.
  Context `{_MEM: !memGS}.

  Context (sp : specmap).
  
  Local Definition MemA := MemA.t sp.
  Local Definition CellioIMod := (CellioI.t ★ MemA).
  Local Definition CellioAMod := (CellioA.t ★ MemA).
  Local Notation IstFull :=
    (λ STATE, (True ∗ IstEq MemA STATE)%I).

  Lemma simF_new `{STATE : !stateGS Σ} :
    ⊢ ISim.sim_fun open CellioAMod CellioIMod IstFull (fid CellioHdr.new).
  Proof using.
    cStartFunSim. rewrite /CellioI.new /new.

    cStepsT. cStepsS. destruct Any.downcast; [|cStepsS; ss].
    cStepsT. cStepsS. cForceS Vnullptr. cStepsS.
    cForceS. iSplit; et. cStepsS. cStep. iFrame. et.
  Qed.

  Lemma simF_push `{STATE : !stateGS Σ} :
    ⊢ ISim.sim_fun open CellioAMod CellioIMod IstFull (fid CellioHdr.push).
  Proof using.
    cStartFunSim. rewrite /CellioI.push /push.

    cStepsS. destruct Any.downcast; cStepsS; des_ifs. cStepsS. cStepsT. 

    cCall "IST" as (?) "IST".
    cStepsS. cStepsT.
    destruct Any.downcast; cStepsS; des_ifs. cStepsT. rename z into v_new.

    mAllocT as (?) "[P0 [P1 _]]". rewrite /scale_int; case_match; ss. cStepsT.
    mStoreT "P0".
    mStoreT "P1".

    cForceS. cStepsS. cForceS. iSplitL "P0 P1 ASM".
    { iExists (blk,0%Z), v. iSplit; et. iFrame. et. }

    cStepsS. cStep. iFrame. et.
  (*SLOW*)Qed.
  
  Lemma simF_pop `{STATE : !stateGS Σ} :
    ⊢ ISim.sim_fun open CellioAMod CellioIMod IstFull (fid CellioHdr.pop).
  Proof using.
    cStartFunSim. rewrite /pop /CellioI.pop.

    cStepsS. cStepsT. destruct Any.downcast; cStepsS; des_ifs. cStepsT. des_if.
    { subst. cStepsT. destruct _q; cycle 1.
      { iDestruct "ASM" as (??) "[% _]". ss. }
      cForceS Vnullptr. cStepsS. cForceS. iSplit; et. cStepsS. cStep.
      iFrame. et.
    }

    destruct _q. { iDestruct "ASM" as "%"; ss. }
    iDestruct "ASM" as ([b o]?) "[-> [[P0 [P1 _]] PT]]". rewrite right_id.
    cStepsT. rewrite /scale_int; case_match; ss. cStepsT.

    mLoadT "P0". mLoadT "P1". mFreeT "P0". mFreeT "P1".

    cForceS. cStepsS. cForceS. iFrame.
    cStepsS. cStep. iFrame. et.
  (*SLOW*)Qed.
  
  Lemma sim :
    CellioA.init_cond ⊢ ISim.t open CellioAMod CellioIMod IstFull.
  Proof using.
    iIntros "INIT".
    iApply (ISim_reflR open CellioA.t CellioI.t MemA
      (λ _ : stateGS Σ, True%I)).
    - mod_tac.
    - mod_tac.
    - intros _. mod_tac.
    - iIntros (STATE fn) "%Hfn".
      repeat rewrite Mod.dom_fnsems_add in Hfn.
      set_unfold in Hfn; des; subst.
      + iApply simF_new.
      + iApply simF_push.
      + iApply simF_pop.
    - iIntros (STATE) "SRC TGT". rewrite /init_cond /=. done.
  Qed.
End CellioIA. End CellioIA.
