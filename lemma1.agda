module lemma1 where

open import DSt
open import CPSt

open import Data.Nat
open import Data.Bool using (true; false) renaming (Bool to 𝔹)
open import Data.Empty
open import Data.Product
open import Function
open import Relation.Nullary
open import Data.Unit using (⊤; tt)
open import Relation.Binary.PropositionalEquality

subst-cont  : {var : cpstyp → Set}{τ₁ τ₂ : typ}{μα : trail}{τ₃ : cpstyp} →
              (k₁ : var τ₃ → cpsvalue[ var ] (cpsT τ₁) →
              cpsterm[ var ] (cpsM μα) → cpsterm[ var ] (cpsT τ₂)) →
              (v : cpsvalue[ var ] τ₃) →
              (k₂ : cpsvalue[ var ] (cpsT τ₁) →
              cpsterm[ var ] (cpsM μα) → cpsterm[ var ] (cpsT τ₂)) → Set

subst-cont {var} {τ₁} {τ₂} {μα} {τ₃} k₁ v k₂ =
  {v₁ : var τ₃ → cpsvalue[ var ] (cpsT τ₁)} →
  {v₂ : var τ₃ → cpsvalue[ var ] (cpsT τ₁) → cpsterm[ var ] cpsM μα} →
  -- {v₃ : cpsvalue[ var ] τ₃} →
  {v₁′ : cpsvalue[ var ] (cpsT τ₁)} →
  {v₂′ : cpsvalue[ var ] (cpsT τ₁) → cpsterm[ var ] cpsM μα} →
  cpsSubstVal (λ x → v₁ x) v v₁′ →
  cpsSubst (λ x → v₂ x (v₁ x)) v (v₂′ v₁′) →
  cpsSubst (λ x → k₁ x (v₁ x) (v₂ x (v₁ x))) v (k₂ v₁′ (v₂′ v₁′) )
  -- cpsSubst v₁ v v₁′ →
  -- cpsSubst (λ y → {!v₂ y!}) v {!!} →
  -- cpsSubst (λ y → {!k₁ y (v₁ y)!}) v {!!}

mutual
  SubstV≠ : {var : cpstyp → Set}{τ₁ τ₂ : cpstyp} →
            {t : cpsvalue[ var ] τ₁} →
            {v : cpsvalue[ var ] τ₂} →
            cpsSubstVal (λ y → t) v t

  SubstV≠ {var} {t = CPSVar x} = sVar≠
  SubstV≠ {var} {t = CPSNum n} = sNum
  SubstV≠ {var} {t = CPSFun e} = sFun λ x → Subst≠
  SubstV≠ {var} {t = CPSId} = sId
  SubstV≠ {var} {t = CPSTrail t} = sTra SubstV≠

  Subst≠  : {var : cpstyp → Set}{τ₁ τ₂ : cpstyp} →
            {t : cpsterm[ var ] τ₁} →
            {v : cpsvalue[ var ] τ₂} →
            cpsSubst (λ y → t) v t

  Subst≠ {t = CPSVal x} = sVal SubstV≠
  Subst≠ {t = CPSApp t t₁} = sApp Subst≠ Subst≠
  Subst≠ {t = CPSLet t x} = sLet (λ y → Subst≠) (λ y₂ → Subst≠)
  Subst≠ {t = CPSPlus t t₁} = sPlu Subst≠ Subst≠
  Subst≠ {t = CPSIdk x x₁ t} = sIdk SubstV≠ Subst≠
  Subst≠ {t = CPSAppend x t t₁} = sApd Subst≠ Subst≠
  Subst≠ {t = CPSCons x t t₁} = sCon Subst≠ Subst≠


mutual
  eSubstV  : {var : cpstyp → Set} {τ₁ τ : typ} →
             {v₁ : var (cpsT τ) → value[ var ∘ cpsT ] τ₁} →
             {v₁′ : value[ var ∘ cpsT ] τ₁} →
             {v : value[ var ∘ cpsT ] τ} →
             SubstVal v₁ v v₁′ →
             cpsSubstVal (λ y → cpsV {var = var} (v₁ y)) (cpsV v) (cpsV v₁′)
             
  eSubstV SubstVal.sVar= = cpsSubstVal.sVar=
  eSubstV SubstVal.sVar≠ = cpsSubstVal.sVar≠
  eSubstV SubstVal.sNum = cpsSubstVal.sNum
  eSubstV (sFun sub) = sFun (λ x → sVal (sFun (λ k → sVal (sFun (λ x₁ →
                       ekSubst' (λ x₂ x₃ → _) (CPSVal (CPSVar x₁)) (sub x))))))

  eSubst   : {var : cpstyp → Set} {τ₁ α β τ : typ} {μα μβ : trail} →
             {e₁ : var (cpsT τ) →
               term[ var ∘ cpsT ] τ₁ ⟨ μα ⟩ α ⟨ μβ ⟩ β} →
             {e₂ : term[ var ∘ cpsT ] τ₁ ⟨ μα ⟩ α ⟨ μβ ⟩ β} →
             {v : value[ var ∘ cpsT ] τ} →
             {k : cpsvalue[ var ] (cpsT τ₁) → cpsterm[ var ] (cpsM μα) → cpsterm[ var ] (cpsT α)} →
             {t :  cpsterm[ var ] cpsM μβ} →
             Subst e₁ v e₂ →
             subst-cont (λ x → k) (cpsV v) k →
             cpsSubst (λ x → cpsTerm (e₁ x) k t) (cpsV v)
             (cpsTerm e₂ k t)

  eSubst (sVal x) eq = eq (eSubstV x) Subst≠
  eSubst (sApp x x₂) eq = ekSubst x (λ x₁ x₃ → ekSubst {!x₂!}
                          (λ x₄ x₅ → sApp (sApp (sVal {!x₄!}) (sVal x₄))
                          (sVal (sFun λ a → eq sVar≠ (sVal {!!})))))
  eSubst (sPlu x x₂) x₁ = ekSubst x (λ x₃ x₄ → ekSubst {!x₂!}
                          (λ x₅ x₆ → sApp (sVal {!x₅!}) {!!}))
  eSubst (sCon x) x₁ = {!!}
  eSubst (sPro x) x₁ = {!!}
  


  ekSubst  : {var : cpstyp → Set} {τ τ₁ α β : typ} {μα μβ : trail} →
             {e₁ : (var ∘ cpsT) τ → term[ var ∘ cpsT ] τ₁ ⟨ μα ⟩ α ⟨ μβ ⟩ β} →
             {e₂ : term[ var ∘ cpsT ] τ₁ ⟨ μα ⟩ α ⟨ μβ ⟩ β} →
             {v : value[ var ∘ cpsT ] τ} →
             {k₁ : var (cpsT τ) → cpsvalue[ var ] (cpsT τ₁) →
             cpsterm[ var ] (cpsM μα) → cpsterm[ var ] (cpsT α)} →
             {k₂ : cpsvalue[ var ] (cpsT τ₁) →
             cpsterm[ var ] (cpsM μα) → cpsterm[ var ] (cpsT α)} →
             {t₁ : cpsterm[ var ] (cpsM μβ)} →
             Subst e₁ v e₂ →
             subst-cont k₁ (cpsV v) k₂ →
             cpsSubst (λ y → cpsTerm (e₁ y) (k₁ y) t₁) (cpsV v)
                     (cpsTerm e₂ k₂ t₁)

  ekSubst (sVal x) eq = eq (eSubstV x) Subst≠
  -- eq Subst≠ (eSubstV x)
  ekSubst (sApp sub₁ sub₂) eq = {!!}
  -- ekSubst sub₁
                                --   λ m n → ekSubst {!sub₂!}
                                --   λ m₂ n₂ → sApp (sApp (sVal {!n!}) (sVal n₂))
                                --   (sVal (sFun (λ x → eq (sVal {!n₂!}) sVar≠)))
  ekSubst (sPlu x x₂) eq = ekSubst x {!eq!}
  ekSubst (sCon x) x₁ = {!!}
  ekSubst (sPro x) x₁ = {!!}


-- ([e₁]′ @ k)[v/y] = [e₂]′ @ k
  ekSubst'  : {var : cpstyp → Set} {τ₁ τ α β : typ} {μα μβ : trail} →
              {e₁ : var (cpsT τ) →
                    term[ var ∘ cpsT ] τ₁ ⟨ μα ⟩ α ⟨ μβ ⟩ β} →
              {e₂ : term[ var ∘ cpsT ] τ₁ ⟨ μα ⟩ α ⟨ μβ ⟩ β} →
              {v : value[ var ∘ cpsT ] τ} →
              (k : cpsvalue[ var ] (cpsT τ₁) → cpsterm[ var ] (cpsM μα) →
              cpsterm[ var ] (cpsT α)) →
              (t : cpsterm[ var ] (cpsM μβ)) →
              Subst e₁ v e₂ →
              cpsSubst (λ x → cpsTerm (e₁ x) k t)
                      (cpsV v)
                      (cpsTerm e₂ k t)

  ekSubst' k t (sVal sub) = {!!}
  ekSubst' k t (sApp sub₁ sub₂) = {!!}
  ekSubst' k t (sPlu x x₁) = {!!}
  ekSubst' k t (sCon x) = {!!}
  ekSubst' k t (sPro x) = {!!}


correctEta : {var : cpstyp → Set} {τ₁ α β : typ} {μα μβ : trail} →
             {e e′ : term[ var ∘ cpsT ] τ₁ ⟨ μα ⟩ α ⟨ μβ ⟩ β} →
             (k : cpsvalue[ var ] (cpsT τ₁) → cpsterm[ var ] (cpsM μα) → cpsterm[ var ] (cpsT α)) →
             (t : cpsterm[ var ] (cpsM μβ)) →
             Reduce e e′ →
             cpsreduce (cpsTerm e k t) (cpsTerm e′ k t)   --⟦ e ⟧k = ⟦ e′ ⟧k

correctEta {e′ = e′} k t (RBeta {e₁ = e₁} {v₂ = v₂} x) = begin
  (cpsTerm (App (Val (Fun e₁)) (Val v₂)) k t)
  ⟶⟨ rApp₁ (rApp₁ (rBeta (sVal (sFun (λ x₁ → sVal (sFun (λ x₂ → eSubst x λ x₃ x₄ → sApp (sApp Subst≠ {!!}) x₄))))))) ⟩
  CPSApp
    (CPSApp
     (CPSVal
      (CPSFun
       (λ z →
          CPSVal
          (CPSFun
           (λ z₁ →
              cpsTerm e′ (λ v → CPSApp (CPSApp (CPSVal (CPSVar z)) (CPSVal v)))
              (CPSVal (CPSVar z₁)))))))
     (CPSVal
      (CPSFun
       (λ v →
          CPSVal (CPSFun (λ t'' → k (CPSVar v) (CPSVal (CPSVar t''))))))))
    t
  ⟶⟨ rApp₁ (rBeta (sVal (sFun (λ x₁ → {!!})))) ⟩
  CPSApp (CPSVal (CPSFun {!!})) t
  ⟶⟨ {!!} ⟩
  (cpsTerm e′ k t)
  ∎
correctEta k t (RPlus {τ₂} {μα} {n₁} {n₂}) = begin
  (CPSLet (CPSPlus (CPSVal (CPSNum n₁)) (CPSVal (CPSNum n₂))) (λ v → k (CPSVar v) t))
  ⟶⟨ rLet₁ rPlus ⟩
  CPSLet (CPSVal (CPSNum (n₁ + n₂))) (λ v → k (CPSVar v) t)
  ⟶⟨ rLet {!!} ⟩
  k (CPSNum (n₁ + n₂)) t
  ∎
  -- (k (CPSNum (n₁ + n₂)) t)

  -- cpsreduce* (cpsTerm (frame-plug f e₁) k t)
  --     (cpsTerm (frame-plug f e₂) k t)

correctEta k t (RFrame  (App₁ e₃) x) = correctEta (λ v₁ →
                                                                         cpsTerm e₃
                                                                         (λ v₂ →
                                                                            CPSApp
                                                                            (CPSApp (CPSApp (CPSVal v₁) (CPSVal v₂))
                                                                             (CPSVal
                                                                              (CPSFun
                                                                               (λ v →
                                                                                  CPSVal (CPSFun (λ t'' → k (CPSVar v) (CPSVal (CPSVar t''))))))))))
                                                                                  t x
correctEta k t (RFrame (App₂ v₁) x) = correctEta (λ v₂ →
                                                     CPSApp
                                                     (CPSApp (CPSApp (CPSVal (cpsV v₁)) (CPSVal v₂))
                                                      (CPSVal
                                                       (CPSFun
                                                        (λ v →
                                                           CPSVal (CPSFun (λ t'' → k (CPSVar v) (CPSVal (CPSVar t''))))))))) t x
correctEta k t (RFrame (Plus₁ e₃) x) = correctEta (λ v₁ →  cpsTerm e₃
                                                                          (λ v₂ t₂ →
                                                                             CPSLet (CPSPlus (CPSVal v₁) (CPSVal v₂)) (λ v → k (CPSVar v) t₂))) t x
correctEta k t (RFrame (Plus₂ v₁) x) = correctEta (λ v₂ t₂ →
                                                      CPSLet (CPSPlus (CPSVal (cpsV v₁)) (CPSVal v₂))
                                                      (λ v → k (CPSVar v) t₂)) t x
correctEta k t (RFrame {e₁ = e₁} {e₂ = e₂} (Pro x₁) x) = begin
  (CPSLet (cpsTerm e₁ (CPSIdk x₁) (CPSVal CPSId))
       (λ v → k (CPSVar v) t))
  ⟶⟨ rLet₁ (correctEta (CPSIdk x₁) (CPSVal CPSId) x) ⟩
  (CPSLet (cpsTerm e₂ (CPSIdk x₁) (CPSVal CPSId))
       (λ v → k (CPSVar v) t))
  ∎
  
correctEta k t (RPrompt {v₁ = v₁}) = begin
  (CPSLet (CPSIdk refl (cpsV v₁) (CPSVal CPSId))
       (λ v → k (CPSVar v) t))
  ⟶⟨ rLet₁ rIdkid ⟩
  CPSLet (CPSVal (cpsV v₁)) (λ v → k (CPSVar v) t)
  ⟶⟨ rLetApp ⟩
  CPSApp (CPSVal (CPSFun (λ v → k (CPSVar v) t))) (CPSVal (cpsV v₁))
  ⟶⟨ rBeta {!!} ⟩
  (k (cpsV v₁) t)
  ∎
correctEta k t (RControl p₁ p₂ x₁ x₂ x₃ x e) = {!!}



