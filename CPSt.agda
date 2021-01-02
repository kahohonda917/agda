module CPSt where

open import rplus
open import Data.Nat
open import Data.Bool using (true; false) renaming (Bool to 𝔹)
open import Data.Empty
open import Data.Product
open import Function
open import Relation.Nullary
open import Data.Unit using (⊤; tt)
open import Relation.Binary.PropositionalEquality


    
--target type
data cpstyp : Set where
  Nat : cpstyp
  Bool : cpstyp
  _⇛_ : cpstyp → cpstyp → cpstyp
  ∙ : cpstyp

--typ transform

mutual
  cpsT : typ → cpstyp
  cpsT Nat = Nat
  cpsT Tbool = Bool
  cpsT (τ₂ ⇒ τ₁ ⟨ μα ⟩ α ⟨ μβ ⟩ β) =
       cpsT τ₂ ⇛ ((cpsT τ₁ ⇛ (cpsM μα ⇛ cpsT α)) ⇛ (cpsM μβ ⇛ cpsT β))

  cpsM : trail → cpstyp
  cpsM ∙ = ∙
  cpsM (τ ⇒ τ' , μ) = (cpsT τ ⇛ cpsM μ) ⇛ cpsT τ'

--target

mutual
  data cpsvalue[_]_ (var : cpstyp → Set) : cpstyp → Set where
    CPSVar : {τ₁ : cpstyp} → var τ₁ → cpsvalue[ var ] τ₁
    CPSNum : ℕ → cpsvalue[ var ] Nat
    CPSFun : {τ₁ τ₂ : cpstyp} → (var τ₂ → cpsterm[ var ] τ₁) →
             cpsvalue[ var ] (τ₂ ⇛ τ₁)

  data cpsterm[_]_ (var : cpstyp → Set) : cpstyp → Set where
    CPSVal    : {τ₁ : cpstyp} → cpsvalue[ var ] τ₁ →
                cpsterm[ var ] τ₁
    CPSApp    : {τ₁ τ₂ : cpstyp} → cpsterm[ var ] (τ₂ ⇛ τ₁) →
                cpsterm[ var ] τ₂ → cpsterm[ var ] τ₁
    CPSLet    : {τ₁ τ₂ : cpstyp} → cpsterm[ var ] τ₁ →
                (var τ₁ → cpsterm[ var ] τ₂) →
                cpsterm[ var ] τ₂
    CPSPlus   : cpsterm[ var ] Nat →
                cpsterm[ var ] Nat →
                cpsterm[ var ] Nat
    CPSId     : cpsterm[ var ] ∙
    CPSTrail  : {τ₁ : cpstyp} → cpsterm[ var ] τ₁ →
                cpsterm[ var ] τ₁
    CPSIdk    : {τ₁ τ₂ : typ} {μ : trail} → is-id-trail τ₁ τ₂ μ →
                cpsvalue[ var ] cpsT τ₁ →
                cpsterm[ var ] cpsM μ → cpsterm[ var ] cpsT τ₂
    CPSAppend : {μ₁ μ₂ μ₃ : trail} → compatible μ₁ μ₂ μ₃ →
                cpsterm[ var ] cpsM μ₁ →
                cpsterm[ var ] cpsM μ₂ → cpsterm[ var ] cpsM μ₃
    CPSCons   : {τ₁ τ₂ : typ}{μ₀ μ₁ μ₂ : trail} → compatible (τ₁ ⇒ τ₂ , μ₁) μ₂ μ₀  →
                cpsterm[ var ] (cpsT τ₁ ⇛ (cpsM μ₁ ⇛ cpsT τ₂)) →
                cpsterm[ var ] cpsM μ₂ → cpsterm[ var ] cpsM μ₀




mutual
  cpsV : {τ₁ : typ} → {var : cpstyp → Set} →
       value[ var ∘ cpsT ] τ₁ → cpsvalue[ var ] (cpsT τ₁)
  cpsV (Var x) = CPSVar x
  cpsV (Num n) = CPSNum n
  cpsV (Fun e) = CPSFun (λ x → CPSVal (CPSFun (λ k' → CPSVal (CPSFun (λ t' →
                 cpsTerm (e x) (λ v t'' →
                 CPSApp (CPSApp (CPSVal (CPSVar k')) (CPSVal v)) t'') (CPSVal (CPSVar t')))))))
       

  cpsTerm : {τ₁ α β : typ}{μα μβ : trail} → {var : cpstyp → Set} →
            term[ var ∘ cpsT ] τ₁ ⟨ μα ⟩ α ⟨ μβ ⟩ β →
            (cpsvalue[ var ] (cpsT τ₁) → cpsterm[ var ] (cpsM μα) → cpsterm[ var ] (cpsT α)) →
            cpsterm[ var ] (cpsM μβ) →
            cpsterm[ var ] (cpsT β)
  cpsTerm  (Val v) k t = k (cpsV v) t

  cpsTerm  (App e₁ e₂) k t = cpsTerm e₁ (λ v₁ t₁ → cpsTerm e₂
                             (λ v₂ t₂ → CPSApp (CPSApp (CPSApp (CPSVal v₁) (CPSVal v₂))
                             (CPSVal (CPSFun (λ v → CPSVal (CPSFun (λ t'' →
                             k (CPSVar v) (CPSVal (CPSVar t'')))))))) t₂) t₁) t
                           
  cpsTerm  (Plus e₁ e₂) k t = cpsTerm e₁ (λ v₁ t₁ → cpsTerm e₂
                              (λ v₂ t₂ → CPSLet (CPSPlus (CPSVal v₁) (CPSVal v₂)) (λ v → k (CPSVar v) t₂)) t₁) t
                            
  cpsTerm  (Control x x₂ x₃ e) k t = CPSLet (CPSVal (CPSFun (λ v →
                                     CPSVal (CPSFun (λ k' → CPSVal (CPSFun (λ t' →
                                     CPSLet (CPSAppend x₃ t
                                     (CPSCons x₂ (CPSVal (CPSVar k')) (CPSVal (CPSVar t'))))
                                     (λ t'' → k (CPSVar v) (CPSVal (CPSVar t''))))))))))
                                     (λ x' → cpsTerm (e x') (CPSIdk x) CPSId)
  
  cpsTerm  (Prompt x e) k t = CPSLet (cpsTerm e (CPSIdk x) CPSId) λ v → k (CPSVar v) t


--cpsframe
data cpsframe[_,_]_ (var : cpstyp → Set) : cpstyp → cpstyp → Set where
  CPSApp₁ : {τ₁ τ₂ : cpstyp} → (e₂ : cpsterm[ var ] τ₂) →
            cpsframe[ var , τ₂ ⇛ τ₁ ] τ₁
  CPSApp₂ : {τ₁ τ₂ : cpstyp} → (v₁ : cpsvalue[ var ] (τ₂ ⇛ τ₁)) →
            cpsframe[ var , τ₂ ] τ₁

cpsframe-plug : {var : cpstyp → Set} → {τ₁ τ₂ : cpstyp} →
                cpsframe[ var , τ₁ ] τ₂ →
                cpsterm[ var ] τ₁ →
                cpsterm[ var ] τ₂
cpsframe-plug (CPSApp₁ e₂) e₁ = CPSApp e₁ e₂
cpsframe-plug (CPSApp₂ v₁) e₂ = CPSApp (CPSVal v₁) e₂

--cpscontext
data cpscontext[_,_]_ (var : cpstyp → Set) : cpstyp → cpstyp → Set where
  CPSHole  : {τ₁ : cpstyp} → cpscontext[ var , τ₁ ] τ₁
  CPSFrame : {τ₁ τ₂ τ₃ : cpstyp} → cpsframe[ var , τ₂ ] τ₃ →
             cpscontext[ var , τ₁ ] τ₂ →
             cpscontext[ var , τ₁ ] τ₃


cpscontext-plug : {var : cpstyp → Set} → {τ₁ τ₂ : cpstyp} →
                  cpscontext[ var , τ₁ ] τ₂ →
                  cpsterm[ var ] τ₁ →
                  cpsterm[ var ] τ₂
cpscontext-plug CPSHole e₁ = e₁
cpscontext-plug (CPSFrame f p) e₁ = cpsframe-plug f (cpscontext-plug p e₁)


--subst
mutual
  data cpsSubstVal {var : cpstyp → Set} : {τ₁ τ₂ : cpstyp} →
                   (var τ₁ → cpsvalue[ var ] τ₂) →
                   cpsvalue[ var ] τ₁ →
                   cpsvalue[ var ] τ₂ → Set where

    sVar= : {τ₁ : cpstyp} {v : cpsvalue[ var ] τ₁} →
            cpsSubstVal (λ x → CPSVar x) v v
            
    sVar≠ : {τ₁ τ₂ : cpstyp} {v : cpsvalue[ var ] τ₂} {x : var τ₁} →
            cpsSubstVal (λ _ → CPSVar x) v (CPSVar x)
            
    sNum  : {τ₁ : cpstyp} {v : cpsvalue[ var ] τ₁} {n : ℕ} →
            cpsSubstVal (λ _ → CPSNum n) v (CPSNum n)

    sFun  : {τ τ₁ τ₂ : cpstyp} →
            {e₁ : var τ → var τ₁ → cpsterm[ var ] τ₂} →
            {v : cpsvalue[ var ] τ} →
            {e₁′ : var τ₁ → cpsterm[ var ] τ₂} →
            ((x : var τ₁) → cpsSubst (λ y → (e₁ y) x) v (e₁′ x)) →
            cpsSubstVal (λ y → CPSFun (e₁ y)) v (CPSFun e₁′)


  data cpsSubst {var : cpstyp → Set} : {τ₁ τ₂ : cpstyp} →
                (var τ₁ → cpsterm[ var ] τ₂) →
                cpsvalue[ var ] τ₁ →
                cpsterm[ var ] τ₂ → Set where

    sVal : {τ τ₁ : cpstyp} →
           {v₁ : var τ → cpsvalue[ var ] τ₁} →
           {v : cpsvalue[ var ] τ} →
           {v₁′ : cpsvalue[ var ] τ₁} →
           cpsSubstVal v₁ v v₁′ →
           cpsSubst (λ y → CPSVal (v₁ y)) v (CPSVal v₁′)

    sApp : {τ τ₁ τ₂ : cpstyp} →
           {e₁ : var τ → cpsterm[ var ] (τ₂ ⇛ τ₁)} →
           {e₂ : var τ → cpsterm[ var ] τ₂} →
           {v : cpsvalue[ var ] τ} →
           {e₁′ : cpsterm[ var ] (τ₂ ⇛ τ₁)} →
           {e₂′ : cpsterm[ var ] τ₂} →
           cpsSubst e₁ v e₁′ → cpsSubst e₂ v e₂′ →
           cpsSubst (λ y → CPSApp (e₁ y) (e₂ y)) v (CPSApp e₁′ e₂′)

    sLet : {τ τ₁ τ₂ : cpstyp} →
           {e₁ : var τ₁ → cpsterm[ var ] τ} →
           {e₂ : var τ₁ → var τ → cpsterm[ var ] τ₂} →
           {v : cpsvalue[ var ] τ₁} →
           {e₁′ : cpsterm[ var ] τ} →
           {e₂′ : var τ → cpsterm[ var ] τ₂} →
           ((x : var τ) → cpsSubst (λ y → (e₂ y) x) v (e₂′ x)) →
           ((x : var τ) → cpsSubst (λ y → e₁ y) v e₁′) →
           cpsSubst (λ y → CPSLet (e₁ y) (e₂ y)) v (CPSLet e₁′ e₂′)

    sPlu : {τ : cpstyp} →
           {e₁ : var τ → cpsterm[ var ] Nat} →
           {e₂ : var τ → cpsterm[ var ] Nat} →
           {v : cpsvalue[ var ] τ} →
           {e₁′ : cpsterm[ var ] Nat} →
           {e₂′ : cpsterm[ var ] Nat} →
           cpsSubst e₁ v e₁′ → cpsSubst e₂ v e₂′ →
           cpsSubst (λ y → CPSPlus (e₁ y) (e₂ y)) v (CPSPlus e₁′ e₂′)

    sId  : {τ : cpstyp} → {v : cpsvalue[ var ] τ} →
           cpsSubst (λ x → CPSId) v CPSId

    sTra : {τ τ₁ : cpstyp} →
           {e : var τ → cpsterm[ var ] τ₁} →
           {v : cpsvalue[ var ] τ} →
           {e′ : cpsterm[ var ] τ₁} →
           cpsSubst e v e′ →
           cpsSubst (λ y → CPSTrail (e y)) v (CPSTrail e′)

    sIdk : {τ : cpstyp} {τ₁ τ₂ : typ} {μ : trail} →
           {x : is-id-trail τ₁ τ₂ μ} →
           {e₁ : var τ → cpsvalue[ var ] cpsT τ₁} →
           {e₂ : var τ → cpsterm[ var ] cpsM μ} →
           {v : cpsvalue[ var ] τ} →
           {e₁′ : cpsvalue[ var ] cpsT τ₁} →
           {e₂′ : cpsterm[ var ] cpsM μ} →
           cpsSubstVal e₁ v e₁′ → cpsSubst e₂ v e₂′ →
           cpsSubst (λ y → CPSIdk x (e₁ y) (e₂ y)) v (CPSIdk x e₁′ e₂′)

    sApd : {τ : cpstyp} {μ₁ μ₂ μ₃ : trail} →
           {x : compatible μ₁ μ₂ μ₃} →
           {e₁ : var τ → cpsterm[ var ] cpsM μ₁} →
           {e₂ : var τ → cpsterm[ var ] cpsM μ₂} →
           {v : cpsvalue[ var ] τ} →
           {e₁′ : cpsterm[ var ] cpsM μ₁} →
           {e₂′ : cpsterm[ var ] cpsM μ₂} →
           cpsSubst e₁ v e₁′ → cpsSubst e₂ v e₂′ →
           cpsSubst (λ y → CPSAppend x (e₁ y) (e₂ y)) v (CPSAppend x e₁′ e₂′)

    sCon : {τ : cpstyp} {τ₁ τ₂ : typ} {μ₀ μ₁ μ₂ : trail} →
           {x : compatible (τ₁ ⇒ τ₂ , μ₁) μ₂ μ₀} →
           {e₁ : var τ → cpsterm[ var ] (cpsT τ₁ ⇛ (cpsM μ₁ ⇛ cpsT τ₂))} →
           {e₂ : var τ → cpsterm[ var ] cpsM μ₂} →
           {v : cpsvalue[ var ] τ} →
           {e₁′ : cpsterm[ var ] (cpsT τ₁ ⇛ (cpsM μ₁ ⇛ cpsT τ₂))} →
           {e₂′ : cpsterm[ var ] cpsM μ₂} →
           cpsSubst e₁ v e₁′ → cpsSubst e₂ v e₂′ →
           cpsSubst (λ y → CPSCons x (e₁ y) (e₂ y)) v (CPSCons x e₁′ e₂′)

 
                
data cpsreduce {var : cpstyp → Set} : {τ₁ : cpstyp} →
              cpsterm[ var ] τ₁ →
              cpsterm[ var ] τ₁ → Set where

  rBeta    : {τ τ₁ : cpstyp} →
              {e₁ : var τ → cpsterm[ var ] τ₁} →
              {v : cpsvalue[ var ] τ} →
              {e₁′ : cpsterm[ var ] τ₁} →
              cpsSubst e₁ v e₁′ →
              cpsreduce (CPSApp (CPSVal (CPSFun e₁)) (CPSVal v)) e₁′

  rLet     : {τ τ₁ : cpstyp} →
              {v : cpsvalue[ var ] τ} →
              {e₁ : var τ → cpsterm[ var ] τ₁} →
              {e₁′ : cpsterm[ var ] τ₁} →
              cpsSubst e₁ v e₁′ →
              cpsreduce (CPSLet (CPSVal v) e₁) e₁′

  rPlus    : {n₁ : ℕ} →
              {n₂ : ℕ} →
              cpsreduce (CPSPlus (CPSVal (CPSNum n₁)) (CPSVal (CPSNum n₂)))
              (CPSVal (CPSNum (n₁ + n₂)))
