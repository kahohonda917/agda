module CPSt3 where

open import DSt2

open import Data.Nat using (ℕ; _+_)
open import Function using (_∘_)
open import Relation.Binary.PropositionalEquality using (refl; _≡_)

-- CPS (target) types
data cpstyp : Set where
  Nat  : cpstyp
  Bool : cpstyp
  _⇛_  : cpstyp → cpstyp → cpstyp
  ∙    : cpstyp

-- CPS transformation of types
mutual
  cpsT : typ → cpstyp
  cpsT Nat = Nat
  cpsT Tbool = Bool
  cpsT (τ₂ ⇒ τ₁ ⟨ μs ⟩ α ⟨ μβ ⟩ β) =
       cpsT τ₂ ⇛ ((cpsT τ₁ ⇛ (cpsMs μs ⇛ cpsT α)) ⇛ (cpsM μβ ⇛ cpsT β))

  cpsM : trail → cpstyp
  cpsM ∙ = ∙
  cpsM (τ ⇒ τ' , μ) = cpsT τ ⇛ (cpsM μ ⇛ cpsT τ')

  cpsMs : {μα μβ : trail} → (μs : trails[ μβ ] μα) → cpstyp
  cpsMs {μα}μs = cpsM μα

-- CPS values and terms
mutual
  data cpsvalue[_]_ (var : cpstyp → Set) : cpstyp → Set where
    CPSVar    : {τ₁ : cpstyp} → var τ₁ → cpsvalue[ var ] τ₁
    CPSNum    : ℕ → cpsvalue[ var ] Nat
    CPSFun    : {τ₁ τ₂ : cpstyp} → (var τ₂ → cpsterm[ var ] τ₁) →
                cpsvalue[ var ] (τ₂ ⇛ τ₁)
    CPSIdt    : cpsvalue[ var ] ∙

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
    CPSIdk    : {τ₁ τ₂ : typ} {μ : trail} → is-id-trail τ₁ τ₂ μ →
                cpsterm[ var ] cpsT τ₁ →
                cpsterm[ var ] cpsM μ → cpsterm[ var ] cpsT τ₂
    CPSAppend : {μ₁ μ₂ μ₃ : trail} → compatible μ₁ μ₂ μ₃ →
                cpsterm[ var ] cpsM μ₁ →
                cpsterm[ var ] cpsM μ₂ → cpsterm[ var ] cpsM μ₃
    CPSCons   : {μ₀ μ₁ μ₂ : trail} → compatible μ₁ μ₂ μ₀ →
                cpsterm[ var ] cpsM μ₁ →
                cpsterm[ var ] cpsM μ₂ → cpsterm[ var ] cpsM μ₀

-- CPS transformation
mutual
  cpsV : {τ₁ : typ} → {var : cpstyp → Set} →
         value[ var ∘ cpsT ] τ₁ → cpsvalue[ var ] (cpsT τ₁)
  cpsV (Var x) = CPSVar x
  cpsV (Num n) = CPSNum n
  cpsV (Fun e) =
    CPSFun (λ x → CPSVal (CPSFun (λ k' → CPSVal (CPSFun (λ t' →
      cpsTerm (e x)
        (λ v t'' → CPSApp (CPSApp (CPSVal (CPSVar k')) (CPSVal v))
                          (CPSVal t''))
        (CPSVar t'))))))

  cpsTerm : {τ₁ α β : typ} {μα μβ : trail} {μs : trails[ μβ ] μα} →
            {var : cpstyp → Set} →
            term[ var ∘ cpsT ] τ₁ ⟨ μs ⟩ α ⟨ μβ ⟩ β →
            (cpsvalue[ var ] (cpsT τ₁) → cpsvalue[ var ] (cpsMs μs) →
             cpsterm[ var ] (cpsT α)) →
            cpsvalue[ var ] (cpsM μβ) →
            cpsterm[ var ] (cpsT β)
  cpsTerm  (Val v) k t = k (cpsV v) t

  cpsTerm  (App e₁ e₂) k t =
    cpsTerm e₁ (λ v₁ t₁ →
      cpsTerm e₂ (λ v₂ t₂ →
        CPSApp (CPSApp (CPSApp (CPSVal v₁) (CPSVal v₂))
                       (CPSVal (CPSFun (λ v → CPSVal (CPSFun (λ t'' →
                         k (CPSVar v) (CPSVar t'')))))))
               (CPSVal t₂)) t₁) t

  cpsTerm  (Plus e₁ e₂) k t =
    cpsTerm e₁ (λ v₁ t₁ →
      cpsTerm e₂ (λ v₂ t₂ →
        CPSLet (CPSPlus (CPSVal v₁) (CPSVal v₂))
               (λ v → k (CPSVar v) t₂)) t₁) t

  cpsTerm  (Control id c₁ c₂ e) k t =
    CPSLet (CPSVal (CPSFun (λ v → CPSVal (CPSFun (λ k' →
             CPSVal (CPSFun (λ t' →
               CPSLet (CPSAppend c₂ (CPSVal t)
                                 (CPSCons c₁ (CPSVal (CPSVar k'))
                                             (CPSVal (CPSVar t'))))
                      (λ t'' → k (CPSVar v) (CPSVar t'')))))))))
           (λ x' → cpsTerm (e x')
                     (λ v t → CPSIdk id (CPSVal v) (CPSVal t)) CPSIdt)

  cpsTerm  (Prompt id e) k t =
    CPSLet (cpsTerm e (λ v t → CPSIdk id (CPSVal v) (CPSVal t)) CPSIdt)
           (λ v → k (CPSVar v) t)

-- substitution relation
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

    sId  : {τ : cpstyp} → {v : cpsvalue[ var ] τ} →
           cpsSubstVal (λ _ → CPSIdt) v CPSIdt

{-  sTra : {τ τ₁ : cpstyp} →
           {e : var τ → cpsvalue[ var ] τ₁} →
           {v : cpsvalue[ var ] τ} →
           {e′ : cpsvalue[ var ] τ₁} →
           cpsSubstVal e v e′ →
           cpsSubstVal (λ y → (e y)) v e′ -}

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

    sIdk : {τ : cpstyp} {τ₁ τ₂ : typ} {μ : trail} →
           {id : is-id-trail τ₁ τ₂ μ} →
           {e₁ : var τ → cpsterm[ var ] cpsT τ₁} →
           {e₂ : var τ → cpsterm[ var ] cpsM μ} →
           {v : cpsvalue[ var ] τ} →
           {e₁′ : cpsterm[ var ] cpsT τ₁} →
           {e₂′ : cpsterm[ var ] cpsM μ} →
           cpsSubst e₁ v e₁′ → cpsSubst e₂ v e₂′ →
           cpsSubst (λ y → CPSIdk id (e₁ y) (e₂ y)) v (CPSIdk id e₁′ e₂′)

    sApd : {τ : cpstyp} {μ₁ μ₂ μ₃ : trail} →
           {c : compatible μ₁ μ₂ μ₃} →
           {e₁ : var τ → cpsterm[ var ] cpsM μ₁} →
           {e₂ : var τ → cpsterm[ var ] cpsM μ₂} →
           {v : cpsvalue[ var ] τ} →
           {e₁′ : cpsterm[ var ] cpsM μ₁} →
           {e₂′ : cpsterm[ var ] cpsM μ₂} →
           cpsSubst e₁ v e₁′ → cpsSubst e₂ v e₂′ →
           cpsSubst (λ y → CPSAppend c (e₁ y) (e₂ y)) v
                    (CPSAppend c e₁′ e₂′)

    sCon : {τ : cpstyp} {μ₀ μ₁ μ₂ : trail} →
           {c : compatible μ₁ μ₂ μ₀} →
           {e₁ : var τ → cpsterm[ var ] cpsM μ₁} →
           {e₂ : var τ → cpsterm[ var ] cpsM μ₂} →
           {v : cpsvalue[ var ] τ} →
           {e₁′ : cpsterm[ var ] cpsM μ₁} →
           {e₂′ : cpsterm[ var ] cpsM μ₂} →
           cpsSubst e₁ v e₁′ → cpsSubst e₂ v e₂′ →
           cpsSubst (λ y → CPSCons c (e₁ y) (e₂ y)) v (CPSCons c e₁′ e₂′)

-- reduction relation
data cpsReduce {var : cpstyp → Set} : {τ₁ : cpstyp} →
              cpsterm[ var ] τ₁ →
              cpsterm[ var ] τ₁ → Set where

  -- proper reduction

  rBeta    : {τ τ₁ : cpstyp} →
             {e₁ : var τ → cpsterm[ var ] τ₁} →
             {v : cpsvalue[ var ] τ} →
             {e₁′ : cpsterm[ var ] τ₁} →
             cpsSubst e₁ v e₁′ →
             cpsReduce (CPSApp (CPSVal (CPSFun e₁)) (CPSVal v)) e₁′

  rPlus    : {n₁ n₂ : ℕ} →
             cpsReduce (CPSPlus (CPSVal (CPSNum n₁)) (CPSVal (CPSNum n₂)))
             (CPSVal (CPSNum (n₁ + n₂)))

  rLet     : {τ τ₁ : cpstyp} →
             {v : cpsvalue[ var ] τ} →
             {e₁ : var τ → cpsterm[ var ] τ₁} →
             {e₁′ : cpsterm[ var ] τ₁} →
             cpsSubst e₁ v e₁′ →
             cpsReduce (CPSLet (CPSVal v) e₁) e₁′

  -- proper reduction for idk, cons, and append

  rIdkid   : {τ₁ : typ} →
             {v : cpsvalue[ var ] cpsT τ₁} →
             cpsReduce (CPSIdk refl (CPSVal v) (CPSVal CPSIdt)) (CPSVal v)

  rIdkt    : {τ₁ τ₂ : typ} →
             {id : is-id-trail τ₁ τ₂ (τ₁ ⇒ τ₂ , ∙)} →
             {v : cpsvalue[ var ] cpsT τ₁} →
             {k : cpsvalue[ var ] (cpsT τ₁ ⇛ (∙ ⇛ cpsT τ₂))} →
             cpsReduce (CPSIdk id (CPSVal v) (CPSVal k))
                       (CPSApp (CPSApp (CPSVal k) (CPSVal v)) (CPSVal CPSIdt))

  rConsid  : {τ₁ τ₂ : typ} {μ₁ : trail} →
             {v : cpsvalue[ var ] (cpsT τ₁ ⇛ (cpsM μ₁ ⇛ cpsT τ₂))} →
             cpsReduce (CPSCons refl (CPSVal v) (CPSVal CPSIdt)) (CPSVal v)

{-
  rConsid₂  : {τ₁ τ₂ : typ} {μ₁ : trail} →
              {v₁ : cpsvalue[ var ] (cpsT τ₁ ⇛ (cpsM μ₁ ⇛ cpsT τ₂))} →
              {id : cpsvalue[ var ] ∙} →
              cpsReduce (CPSVal (CPSCons refl v₁ id)) (CPSVal v₁)
-}

  rConst   : {τ₁ τ₂ : typ} {μ₁ μ₁' μ₂' : trail} →
             {c₁ : compatible (τ₁ ⇒ τ₂ , μ₁) μ₁'
                              (τ₁ ⇒ τ₂ , μ₂') } →
             {c₂ : compatible μ₁' μ₂' μ₁}
             {k : cpsvalue[ var ] (cpsT τ₁ ⇛ (cpsM μ₁ ⇛ cpsT τ₂))} →
             {k′ : cpsvalue[ var ] cpsM μ₁'} →
             cpsReduce
               (CPSCons c₁ (CPSVal k) (CPSVal k′))
               (CPSVal (CPSFun (λ v → CPSVal (CPSFun (λ t' →
                 CPSApp (CPSApp (CPSVal k) (CPSVal (CPSVar v)))
                        (CPSCons c₂ (CPSVal k′) (CPSVal (CPSVar t'))))))))

{-
  rConst   : {τ₁ τ₁' τ₂ τ₂' : typ} {μ₁ μ₁' μ₂' : trail} →
             {c₁ : compatible (τ₁ ⇒ τ₂ , μ₁) (τ₁' ⇒ τ₂' , μ₁')
                              (τ₁ ⇒ τ₂ , μ₂') } →
             {c₂ : compatible (τ₁' ⇒ τ₂' , μ₁') μ₂' μ₁}
             {k : cpsvalue[ var ] (cpsT τ₁ ⇛ (cpsM μ₁ ⇛ cpsT τ₂))} →
             {k′ : cpsvalue[ var ] (cpsT τ₁' ⇛ (cpsM μ₁' ⇛ cpsT τ₂'))} →
             cpsReduce
               (CPSCons c₁ (CPSVal k) (CPSVal k′))
               (CPSVal (CPSFun (λ v → CPSVal (CPSFun (λ t' →
                 CPSApp (CPSApp (CPSVal k) (CPSVal (CPSVar v)))
                        (CPSCons c₂ (CPSVal k′) (CPSVal (CPSVar t'))))))))
-}

  rApdid   : {μ₂ : trail} →
             {v : cpsvalue[ var ] cpsM μ₂} →
             cpsReduce (CPSAppend refl (CPSVal CPSIdt) (CPSVal v)) (CPSVal v)

  rApdt    : {τ₁ τ₂ : typ} {μ₁ μ₂ μ₃ : trail} →
             {c : compatible (τ₁ ⇒ τ₂ , μ₁) μ₂ μ₃} →
             {k : cpsvalue[ var ] (cpsT τ₁ ⇛ (cpsM μ₁ ⇛ cpsT τ₂))} →
             {t : cpsvalue[ var ] cpsM μ₂} →
             cpsReduce (CPSAppend c (CPSVal k) (CPSVal t))
                       (CPSCons c (CPSVal k) (CPSVal t))

  -- reduction under evaluation context

  rApp₁    : {τ₁ τ₂ : cpstyp} →
             {e₁ e₁′ : cpsterm[ var ] (τ₂ ⇛ τ₁)} →
             {e₂ : cpsterm[ var ] τ₂} →
             cpsReduce e₁ e₁′ →
             cpsReduce (CPSApp e₁ e₂) (CPSApp e₁′ e₂)

  rApp₂    : {τ₁ τ₂ : cpstyp} →
             {v₁ : cpsvalue[ var ] (τ₂ ⇛ τ₁)} →
             {e₂ e₂′ : cpsterm[ var ] τ₂} →
             cpsReduce e₂ e₂′ →
             cpsReduce (CPSApp (CPSVal v₁) e₂) (CPSApp (CPSVal v₁) e₂′)

  rLet₁    : {τ₁ τ₂ : cpstyp} →
             {e₁ e₁′ : cpsterm[ var ] τ₁} →
             {e₂ : var τ₁ → cpsterm[ var ] τ₂} →
             cpsReduce e₁ e₁′ →
             cpsReduce (CPSLet e₁ e₂) (CPSLet e₁′ e₂)

  rIdk₂    : {τ₁ τ₂ : typ} →
             {id : is-id-trail τ₁ τ₂ (τ₁ ⇒ τ₂ , ∙)} →
             {v : cpsvalue[ var ] cpsT τ₁} →
             {k k′ : cpsterm[ var ] (cpsT τ₁ ⇛ (∙ ⇛ cpsT τ₂))} →
             cpsReduce k k′ →
             cpsReduce (CPSIdk id (CPSVal v) k)
                       (CPSIdk id (CPSVal v) k′)

  rCon₁    : {τ₁ τ₂ : typ} {μ₀ μ₁ μ₂ : trail} →
             {c : compatible (τ₁ ⇒ τ₂ , μ₁) μ₂ μ₀} →
             {e₁ e₁′ : cpsterm[ var ] (cpsT τ₁ ⇛ (cpsM μ₁ ⇛ cpsT τ₂))} →
             {e₂ : cpsterm[ var ] cpsM μ₂} →
             cpsReduce e₁ e₁′ →
             cpsReduce (CPSCons c e₁ e₂) (CPSCons c e₁′ e₂)

  rCon₂    : {τ₁ τ₂ : typ} {μ₀ μ₁ μ₂ : trail} →
             {c : compatible (τ₁ ⇒ τ₂ , μ₁) μ₂ μ₀}  →
             {e₁ : cpsterm[ var ] (cpsT τ₁ ⇛ (cpsM μ₁ ⇛ cpsT τ₂))} →
             {e₂ e₂′ : cpsterm[ var ] cpsM μ₂} →
             cpsReduce e₂ e₂′ →
             cpsReduce (CPSCons c e₁ e₂) (CPSCons c e₁ e₂′)

  rAppend₁ : {μ₁ μ₂ μ₃ : trail} →
             {c : compatible μ₁ μ₂ μ₃} →
             {e₁ e₁′ : cpsterm[ var ] cpsM μ₁} →
             {e₂ : cpsterm[ var ] cpsM μ₂} →
             cpsReduce e₁ e₁′ →
             cpsReduce (CPSAppend c e₁ e₂)
                       (CPSAppend c e₁′ e₂)

  rAppend₂ : {μ₁ μ₂ μ₃ : trail} →
             {c : compatible μ₁ μ₂ μ₃} →
             {e₁ : cpsterm[ var ] cpsM μ₁} →
             {e₂ e₂′ : cpsterm[ var ] cpsM μ₂} →
             cpsReduce e₂ e₂′ →
             cpsReduce (CPSAppend c e₁ e₂)
                       (CPSAppend c e₁ e₂′)

-- beta-equality relation
data cpsEqual {var : cpstyp → Set} : {τ₁ : cpstyp} →
              cpsterm[ var ] τ₁ →
              cpsterm[ var ] τ₁ → Set where

  eReduce  : {τ : cpstyp} {e₁ e₂ : cpsterm[ var ] τ} →
             cpsReduce e₁ e₂ →
             cpsEqual e₁ e₂

  eReduce′ : {τ : cpstyp} {e₁ e₂ : cpsterm[ var ] τ} →
             cpsReduce e₂ e₁ →
             cpsEqual e₁ e₂

  -- reflexive and transitive closure

  e*Id     : {τ : cpstyp} →
             {e : cpsterm[ var ] τ} →
             cpsEqual e e

  e*Trans  : {τ : cpstyp} →
             (e₁ e₂ e₃ : cpsterm[ var ] τ) →
             cpsEqual e₁ e₂ →
             cpsEqual e₂ e₃ →
             cpsEqual e₁ e₃

  e*Trans′ : {τ : cpstyp} →
             (e₁ e₂ e₃ : cpsterm[ var ] τ) →
             cpsEqual e₂ e₁ →
             cpsEqual e₂ e₃ →
             cpsEqual e₁ e₃

  -- equality under evaluation context

  eApp₁    : {τ₁ τ₂ : cpstyp} →
             {e₁ e₁′ : cpsterm[ var ] (τ₂ ⇛ τ₁)} →
             {e₂ : cpsterm[ var ] τ₂} →
             cpsEqual e₁ e₁′ →
             cpsEqual (CPSApp e₁ e₂) (CPSApp e₁′ e₂)

  eApp₂    : {τ₁ τ₂ : cpstyp} →
             {e₁ : cpsterm[ var ] (τ₂ ⇛ τ₁)} →
             {e₂ e₂′ : cpsterm[ var ] τ₂} →
             cpsEqual e₂ e₂′ →
             cpsEqual (CPSApp e₁ e₂) (CPSApp e₁ e₂′)

  eLet₁    : {τ₁ τ₂ : cpstyp} →
             {e₁ e₁′ : cpsterm[ var ] τ₁} →
             {e₂ : var τ₁ → cpsterm[ var ] τ₂} →
             cpsEqual e₁ e₁′ →
             cpsEqual (CPSLet e₁ e₂) (CPSLet e₁′ e₂)

  eCon₁    : {τ₁ τ₂ : typ} {μ₀ μ₁ μ₂ : trail} →
             {c : compatible (τ₁ ⇒ τ₂ , μ₁) μ₂ μ₀} →
             {e₁ e₁′ : cpsterm[ var ] (cpsT τ₁ ⇛ (cpsM μ₁ ⇛ cpsT τ₂))} →
             {e₂ : cpsterm[ var ] cpsM μ₂} →
             cpsEqual e₁ e₁′ →
             cpsEqual (CPSCons c e₁ e₂) (CPSCons c e₁′ e₂)

  eCon₂    : {τ₁ τ₂ : typ} {μ₀ μ₁ μ₂ : trail} →
             {c : compatible (τ₁ ⇒ τ₂ , μ₁) μ₂ μ₀}  →
             {e₁ : cpsterm[ var ] (cpsT τ₁ ⇛ (cpsM μ₁ ⇛ cpsT τ₂))} →
             {e₂ e₂′ : cpsterm[ var ] cpsM μ₂} →
             cpsEqual e₂ e₂′ →
             cpsEqual (CPSCons c e₁ e₂) (CPSCons c e₁ e₂′)

  eAppend₁ : {μ₁ μ₂ μ₃ : trail} →
             {c : compatible μ₁ μ₂ μ₃} →
             {e₁ e₁′ : cpsterm[ var ] cpsM μ₁} →
             {e₂ : cpsterm[ var ] cpsM μ₂} →
             cpsEqual e₁ e₁′ →
             cpsEqual (CPSAppend c e₁ e₂)
                      (CPSAppend c e₁′ e₂)

  eAppend₂ : {μ₁ μ₂ μ₃ : trail} →
             {c : compatible μ₁ μ₂ μ₃} →
             {e₁ : cpsterm[ var ] cpsM μ₁} →
             {e₂ e₂′ : cpsterm[ var ] cpsM μ₂} →
             cpsEqual e₂ e₂′ →
             cpsEqual (CPSAppend c e₁ e₂)
                      (CPSAppend c e₁ e₂′)

  -- equality under binders

  eFun     : {τ₁ τ₂ : cpstyp} →
             {e₁ e₂ : var τ₂ → cpsterm[ var ] τ₁} →
             ((x : var τ₂) → cpsEqual (e₁ x) (e₂ x)) →
             cpsEqual (CPSVal (CPSFun (λ x → e₁ x)))
                      (CPSVal (CPSFun (λ x → e₂ x)))

  eLet₂    : {τ₁ τ₂ : cpstyp} →
             {e₁ : cpsterm[ var ] τ₁} →
             {e₂ e₂′ : var τ₁ → cpsterm[ var ] τ₂} →
             ((x : var τ₁) → cpsEqual (e₂ x) (e₂′ x)) →
             cpsEqual (CPSLet e₁ e₂) (CPSLet e₁ e₂′)

  -- other required equalities

  -- (let x = e1 in e2) e3 <-> let x = e1 in e2 e3
  eLet₃    : {τ₁ τ₂ τ₃ : cpstyp} →
             {e₁ : cpsterm[ var ] τ₁} →
             {e₂ : var τ₁ → cpsterm[ var ] (τ₂ ⇛ τ₃)} →
             {e₃ : cpsterm[ var ] τ₂} →
             cpsEqual (CPSApp (CPSLet e₁ (λ x → e₂ x)) e₃)
                      (CPSLet e₁ (λ x → CPSApp (e₂ x) e₃))

  -- let x = e1 in e2 <-> (fun x -> e2) e1
  eLetApp  : {τ₁ τ₂ : cpstyp} →
             {e₁ : cpsterm[ var ] τ₁} →
             {e₂ : var τ₁ → cpsterm[ var ] τ₂} →
             cpsEqual (CPSLet e₁ (λ x → e₂ x))
                      (CPSApp (CPSVal (CPSFun (λ x → e₂ x))) e₁)

  {-
  -- idk v (k::t) <-> k v t
  eIdkt    : {α τ₂ : typ} {μ₀ μ₁ μα μ₃ : trail} →
             {μ[∙]μ₃ : trails[ ∙ ] μ₃} →
             {μ[μα]μ₃ : trails[ μα ] μ₃} →
             {id : is-id-trails τ₂ α μ[∙]μ₃} →
             {v : cpsvalue[ var ] cpsT τ₂} →
             {c : compatible (τ₂ ⇒ α , μ₃) μ₃ μ₃} →
             {k : cpsvalue[ var ] (cpsT τ₂ ⇛ (cpsMs μ[μα]μ₃ ⇛ cpsT α))} →
             {t : cpsvalue[ var ] cpsMs μ[μα]μ₃} →
             cpsEqual
              (CPSIdk id (CPSVal v) (CPSCons c (CPSVal k) (CPSVal t)))
              (CPSApp (CPSApp (CPSVal k) (CPSVal v)) (CPSVal t))
  -}

  {-
  Goal: cpsEqual
        (CPSIdk id₀ (CPSVal (cpsV v))
         (CPSCons (extend-compatible' c₁ (proj₂ (diff-compatible μ[μα]μ₃)))
          (CPSVal (CPSVar x₁)) (CPSVal t₁)))
        (CPSApp (CPSApp (CPSVal (CPSVar x₁)) (CPSVal (cpsV v)))
         (CPSVal t₁))
  ————————————————————————————————————————————————————————————
  t₁      : cpsvalue[ (λ v₁ → var v₁) ] cpsMs μ[μα]μ₃
  v       : value[ (λ v₁ → var v₁) ∘ cpsT ] τ₂
  x₂      : var (cpsM μα)
  x₁      : var (cpsT τ₂ ⇛ (cpsMs μ[μα]μ₃ ⇛ cpsT α))
  x       : var (cpsT τ)
  e       : (var ∘ cpsT) (τ ⇒ τ₂ ⟨ μ[μα]μ₃ ⟩ α ⟨ μα ⟩ α₁) →
            term[ var ∘ cpsT ] γ ⟨ μ[∙]μᵢ ⟩ γ' ⟨ ∙ ⟩ τ₁
  same    : same-pcontext p₁ p₂
  c₁      : compatible (τ₂ ⇒ α , μ₃) μα μα
  id      : is-id-trails γ γ' μ[∙]μᵢ
  id₀     : is-id-trails τ₂ α μ[∙]μ₃
  p₂      : pcontext[ var ∘ cpsT , τ ⟨ [] ⟩ α₁ ⟨ μα ⟩ α₁ ] τ₂ ⟨
            μ[μα]μ₃ ⟩ α ⟨ μα ⟩ α₁
  p₁      : pcontext[ var ∘ cpsT , τ ⟨ μ[∙]α ⟩ α₁ ⟨ ∙ ⟩ τ₁ ] τ₂ ⟨
            μ[∙]μ₃ ⟩ α ⟨ ∙ ⟩ τ₁
  μ[∙]μᵢ  : trails[ ∙ ] μᵢ   (not in scope)
  μ[μα]μ₃ : trails[ μα ] μ₃
  μ[∙]μ₃  : trails[ ∙ ] μ₃
  μ[∙]α   : trails[ ∙ ] μα
  μ₃      : trail   (not in scope)
  μᵢ      : trail   (not in scope)
  μ₀      : trail   (not in scope)
  τ₂      : typ   (not in scope)
  γ'      : typ   (not in scope)
  γ       : typ   (not in scope)
  α₁      : typ   (not in scope)
  τ       : typ   (not in scope)
  sch'    : schematicV′ k
  sch     : schematicV k
  t       : cpsvalue[ var ] cpsM μα
  k       : cpsvalue[ var ] cpsT τ₁ →
            cpsvalue[ var ] cpsMs [] → cpsterm[ var ] cpsT α
  μα      : trail   (not in scope)
  α       : typ   (not in scope)
  τ₁      : typ   (not in scope)
  var     : cpstyp → Set   (not in scope)
  -}

  -- idt @ e <-> let v = e in idt @ v <-> let v = e in v <-> e
  eApdidΩ : {μ₂ : trail} →
             {e : cpsterm[ var ] cpsM μ₂} →
             cpsEqual (CPSAppend refl (CPSVal CPSIdt) e) e

-- equational reasoning
infix  3 _∎
infixr 2 _⟶⟨_⟩_ _⟷⟨_⟩_ _⟷⟨_⟩′_ _⟵⟨_⟩_ _≡⟨_⟩_
infix  1 begin_

begin_ : {var : cpstyp → Set} {τ₁ : cpstyp} →
         {e₁ e₂ : cpsterm[ var ] τ₁ } → cpsEqual e₁ e₂ → cpsEqual e₁ e₂
begin_ eq* = eq*

_⟶⟨_⟩_ : {var : cpstyp → Set} → {τ₁ : cpstyp} →
           (e₁ {e₂ e₃} : cpsterm[ var ] τ₁) →
           cpsReduce e₁ e₂ → cpsEqual e₂ e₃ → cpsEqual e₁ e₃
_⟶⟨_⟩_ e₁ {e₂} {e₃} e₁-red-e₂ e₂-eq*-e₃ =
  e*Trans e₁ e₂ e₃ (eReduce e₁-red-e₂) e₂-eq*-e₃

_⟷⟨_⟩_ : {var : cpstyp → Set} {τ₁ : cpstyp} →
          (e₁ {e₂ e₃} : cpsterm[ var ] τ₁) →
          cpsEqual e₁ e₂ → cpsEqual e₂ e₃ → cpsEqual e₁ e₃
_⟷⟨_⟩_ e₁ {e₂} {e₃} e₁-eq*-e₂ e₂-eq*-e₃ =
  e*Trans e₁ e₂ e₃ e₁-eq*-e₂ e₂-eq*-e₃

_⟷⟨_⟩′_ : {var : cpstyp → Set} {τ₁ : cpstyp} →
          (e₁ {e₂ e₃} : cpsterm[ var ] τ₁) →
          cpsEqual e₂ e₁ → cpsEqual e₂ e₃ → cpsEqual e₁ e₃
_⟷⟨_⟩′_ e₁ {e₂} {e₃} e₂-eq*-e₁ e₂-eq*-e₃ =
  e*Trans′ e₁ e₂ e₃ e₂-eq*-e₁ e₂-eq*-e₃

_⟵⟨_⟩_ : {var : cpstyp → Set} {τ₁ : cpstyp} →
          (e₁ {e₂ e₃} : cpsterm[ var ] τ₁) →
          cpsReduce e₂ e₁ → cpsEqual e₂ e₃ → cpsEqual e₁ e₃
_⟵⟨_⟩_ e₁ {e₂} {e₃} e₂-red-e₁ e₂-eq*-e₃ =
  e*Trans′ e₁ e₂ e₃ (eReduce e₂-red-e₁) e₂-eq*-e₃

_≡⟨_⟩_ : {var : cpstyp → Set} → {τ₁ : cpstyp} →
         (e₁ {e₂ e₃} : cpsterm[ var ] τ₁) →
         e₁ ≡ e₂ → cpsEqual e₂ e₃ → cpsEqual e₁ e₃
_≡⟨_⟩_ e₁ {e₂} {e₃} refl e₂-eq*-e₃ = e₂-eq*-e₃

_∎ : {var : cpstyp → Set} {τ₁ : cpstyp} →
     (e : cpsterm[ var ] τ₁) → cpsEqual e e
_∎ e = e*Id
