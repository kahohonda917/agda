module lemma2 where

open import DSt2
open import CPSt2

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
               cpsvalue[ var ] (cpsM μα) → cpsterm[ var ] (cpsT τ₂)) →
              (v : cpsvalue[ var ] τ₃) →
              (k₂ : cpsvalue[ var ] (cpsT τ₁) →
               cpsvalue[ var ] (cpsM μα) → cpsterm[ var ] (cpsT τ₂)) → Set

subst-cont {var} {τ₁} {τ₂} {μα} {τ₃} k₁ v k₂ =
  {v₁ : var τ₃ → cpsvalue[ var ] (cpsT τ₁)} →
  {v₁′ : cpsvalue[ var ] (cpsT τ₁)} →
  --{t : var τ₃ → cpsvalue[ var ] (cpsM μα)} →
  {t′ : cpsvalue[ var ] (cpsM μα)} →
  cpsSubstVal (λ x → v₁ x) v v₁′ →
  --cpsSubstVal (λ x → t x) v t′ →
  cpsSubst (λ x → k₁ x (v₁ x) (t′)) v (k₂ v₁′ t′)

subst-cont′  : {var : cpstyp → Set}{τ₁ τ₂ : typ}{μα : trail}{τ₃ : cpstyp} →
              (k₁ : var τ₃ → cpsvalue[ var ] (cpsT τ₁) →
               cpsvalue[ var ] (cpsM μα) → cpsterm[ var ] (cpsT τ₂)) →
              (v : cpsvalue[ var ] τ₃) →
              (k₂ : cpsvalue[ var ] (cpsT τ₁) →
               cpsvalue[ var ] (cpsM μα) → cpsterm[ var ] (cpsT τ₂)) → Set

subst-cont′ {var} {τ₁} {τ₂} {μα} {τ₃} k₁ v k₂ =
  --{v₁ : var τ₃ → cpsvalue[ var ] (cpsT τ₁)} →
  {v₁′ : cpsvalue[ var ] (cpsT τ₁)} →
  --{t : var τ₃ → cpsvalue[ var ] (cpsM μα)} →
  {t′ : cpsvalue[ var ] (cpsM μα)} →
  --cpsSubstVal (λ x → v₁ x) v v₁′ →
  --cpsSubstVal (λ x → t x) v t′ →
  cpsSubst (λ x → k₁ x v₁′ (t′)) v (k₂ v₁′ t′)


-- subst-trail  : {var : cpstyp → Set}{τ₁ τ₂ : typ}{μα : trail}{τ₃ : cpstyp} →
--               (t₁ : var τ₃ → cpsvalue[ var ] (cpsM μα)) →
--               (v : cpsvalue[ var ] τ₃) →
--               (t₂ : cpsvalue[ var ] (cpsM μα)) → Set

-- subst-trail {var} {τ₁} {τ₂} {∙} {τ₃} t₁ v t₂ = cpsSubst (λ x → CPSVal CPSId) v (CPSVal CPSId)
-- subst-trail {var} {τ₁} {τ₂} {x ⇒ x₁ , μα} {τ₃} t₁ v t₂ = {!!}
  -- {k : var τ₃ → cpsvalue[ var ] (cpsT τ₁) →
  --              cpsvalue[ var ] (cpsM μα) → cpsterm[ var ] (cpsT τ₂)} →
  -- {k′ : cpsvalue[ var ] (cpsT τ₁) →
  --              cpsvalue[ var ] (cpsM μα) → cpsterm[ var ] (cpsT τ₂)} →
  -- {v₁ : var τ₃ → cpsvalue[ var ] (cpsT τ₁)} →
  -- {v₁′ : cpsvalue[ var ] (cpsT τ₁)} →
  -- cpsSubst (λ x → k x v₁′ t₂) v (k′ v₁′ t₂) →
  -- cpsSubstVal (λ x → v₁ x) v v₁′ →
  -- cpsSubst (λ x → k′ v₁′ (t₁ x)) v (k′ v₁′ t₂)

mutual
  SubstV≠ : {var : cpstyp → Set}{τ₁ τ₂ : cpstyp} →
            {t : cpsvalue[ var ] τ₁} →
            {v : cpsvalue[ var ] τ₂} →
            cpsSubstVal (λ y → t) v t

  SubstV≠ {var} {t = CPSVar x} = sVar≠
  SubstV≠ {var} {t = CPSNum n} = sNum
  SubstV≠ {var} {t = CPSFun e} = sFun λ x → Subst≠
  SubstV≠ {var} {t = CPSId} = sId
  SubstV≠ {t = CPSAppend x t t₁} = sApd SubstV≠ SubstV≠
  SubstV≠ {t = CPSCons x t t₁} = sCon SubstV≠ SubstV≠

  Subst≠  : {var : cpstyp → Set}{τ₁ τ₂ : cpstyp} →
            {t : cpsterm[ var ] τ₁} →
            {v : cpsvalue[ var ] τ₂} →
            cpsSubst (λ y → t) v t

  Subst≠ {t = CPSVal x} = sVal SubstV≠
  Subst≠ {t = CPSApp t t₁} = sApp Subst≠ Subst≠
  Subst≠ {t = CPSLet t x} = sLet (λ y → Subst≠) (λ y₂ → Subst≠)
  Subst≠ {t = CPSPlus t t₁} = sPlu Subst≠ Subst≠
  Subst≠ {t = CPSIdk x x₁ t} = sIdk SubstV≠ SubstV≠
  

mutual

  SubstV-id  : {var : typ → Set}{τ₁ τ₂ : typ} →
               {v₁ : value[ var ] τ₁} →
               {v : value[ var ] τ₂} →
                SubstVal (λ _ → v₁) v v₁

  SubstV-id {var} {τ₁} {τ₂} {Var x} {v} = sVar≠
  SubstV-id {var} {.Nat} {τ₂} {Num n} {v} = sNum
  SubstV-id {var} {.(_ ⇒ _ ⟨ _ ⟩ _ ⟨ _ ⟩ _)} {τ₂} {Fun e₁} {v} = sFun λ x → Subst-id


  Subst-id  : {var : typ → Set}{τ₁ τ₂ α β : typ}{μα μβ : trail} →
              {μs : trails[ μβ ] μα}{t : term[ var ] τ₁ ⟨ μs ⟩ α ⟨ μβ ⟩ β} →
              {v : value[ var ] τ₂} →
                Subst (λ _ → t) v t

  Subst-id {var} {τ₁} {τ₂} {α} {.α} {μα} {.μα}  {t = Val x} {v} = sVal SubstV-id
  Subst-id {var} {τ₁} {τ₂} {α} {β} {μα} {μβ} {t = App t t₁} {v} = sApp Subst-id Subst-id
  Subst-id {var} {.Nat} {τ₂} {α} {β} {μα} {μβ} {t = Plus t t₁} {v} = sPlu Subst-id Subst-id
  Subst-id {var} {τ₁} {τ₂} {α} {β} {μα} {μβ} {t = Control x x₁ x₂ e} {v} = sCon (λ k → Subst-id)
  Subst-id {var} {τ₁} {τ₂} {α} {.α} {μα} {.μα}  {t = Prompt x t} {v} = sPro Subst-id

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
  eSubstV (sFun sub) = sFun (λ x → sVal (sFun (λ x₁ → sVal (sFun (λ x₂ → eSubst (sub x) (λ x₃ → sApp (sApp Subst≠ (sVal x₃)) Subst≠))))))

  eSubst   : {var : cpstyp → Set} {τ₁ α β τ : typ} {μα μβ : trail}{μs : trails[ μβ ] μα} →
             {e₁ : var (cpsT τ) →
               term[ var ∘ cpsT ] τ₁ ⟨ μs ⟩ α ⟨ μβ ⟩ β} →
             {e₂ : term[ var ∘ cpsT ] τ₁ ⟨ μs ⟩ α ⟨ μβ ⟩ β} →
             {v : value[ var ∘ cpsT ] τ} →
             {k : cpsvalue[ var ] (cpsT τ₁) → cpsvalue[ var ] (cpsMs μs) → cpsterm[ var ] (cpsT α)} →
             {t :  cpsvalue[ var ] cpsM μβ} →
             --{sub : subst-cont′ (λ x → k) (cpsV v) k} →
             --{trail : cpsvalue[ var ] cpsM μα} →
             Subst e₁ v e₂ →
             subst-cont (λ x → k) (cpsV v) k →
             cpsSubst (λ x → cpsTerm (e₁ x) k t) (cpsV v)
             (cpsTerm e₂ k t)
--eq eSubstV x
  eSubst (sVal x) eq = eq (eSubstV x)
  eSubst (sApp x x₂) eq = ekSubst x (λ x₁ → ekSubst x₂ (λ x₃ → sApp (sApp (sApp (sVal x₁) (sVal x₃)) Subst≠) Subst≠))
  eSubst (sPlu x x₂) eq = ekSubst x (λ x₁ → ekSubst x₂ (λ x₃ → sLet (λ x₄ → Subst≠) (λ x₄ → sPlu (sVal x₁) (sVal x₃))))
  eSubst (sCon x) eq = sLet (λ x₂ → eSubst (x x₂) (λ x₆ → sIdk x₆ SubstV≠)) (λ x₂ → Subst≠)
  eSubst (sPro x) eq = sLet (λ x₂ → Subst≠) λ x₄ → eSubst x (λ x₅ → sIdk x₅ SubstV≠)


  schematicV : {var : cpstyp → Set} {τ₁ α : typ}{μα : trail} →
             (k : cpsvalue[ var ] (cpsT τ₁) →
                  cpsvalue[ var ] (cpsM μα) → cpsterm[ var ] (cpsT α)) →
              Set
             
  schematicV {var} {τ₁} {μα = μα} k =
             (v : value[ var ∘ cpsT ] τ₁) →
             (t : cpsvalue[ var ] cpsM μα) →
             cpsSubst (λ x → k (CPSVar x) t) (cpsV v) (k (cpsV v) t)

  schematic  : {var : cpstyp → Set} {τ₁ α : typ}{μα : trail} →
               (k : cpsvalue[ var ] (cpsT τ₁) →
                    cpsvalue[ var ] (cpsM μα) → cpsterm[ var ] (cpsT α)) →
              Set
  schematic  {var} {τ₁} {μα = μα} k =
             (v : cpsvalue[ var ] (cpsT τ₁)) →
             (t : cpsvalue[ var ] cpsM μα) →
             cpsSubst (λ x → k (CPSVar x) t) v (k v t)

  schematicV′ : {var : cpstyp → Set} {τ₁ α : typ}{μα : trail} →
             (k : cpsvalue[ var ] (cpsT τ₁) →
                  cpsvalue[ var ] (cpsM μα) → cpsterm[ var ] (cpsT α)) →
              Set
             
  schematicV′ {var} {τ₁} {μα = μα} k =
             (t : cpsvalue[ var ] (cpsM μα)) →
             (v₂ : cpsvalue[ var ] cpsT τ₁) →
             cpsSubst (λ x → k v₂ (CPSVar x)) t (k v₂ t)

  schematicK  : {var : cpstyp → Set} {τ₁ α : typ}{μα : trail}{τ : cpstyp} →
               (k : cpsvalue[ var ] τ → cpsvalue[ var ] (cpsT τ₁) →
                    cpsvalue[ var ] (cpsM μα) → cpsterm[ var ] (cpsT α)) →
              Set
  schematicK  {var} {τ₁} {μα = μα}{τ = τ} k =
             {v : cpsvalue[ var ] τ} →
             (x : cpsvalue[ var ] (cpsT τ₁)) →
             (t : cpsvalue[ var ] cpsM μα) →
             cpsSubst (λ x₁ → k (CPSVar x₁) x t) v (k v x t)
             --cpsSubst (λ x → k (CPSVar x) t) v (k v t)
  schematicK′  : {var : cpstyp → Set} {τ₁ α : typ}{μα : trail}{τ : cpstyp} →
               (k : var τ → cpsvalue[ var ] (cpsT τ₁) →
                    cpsvalue[ var ] (cpsM μα) → cpsterm[ var ] (cpsT α)) →
              Set
  schematicK′  {var} {τ₁}{α} {μα = μα}{τ = τ} k =
             -- {m : var τ → cpsvalue[ var ] (cpsT τ₁)}→
             -- {x₁′ : cpsvalue[ var ] (cpsT τ₁)} →
             {v : var τ} →
             (x : cpsvalue[ var ] (cpsT τ₁)) →
             (t : cpsvalue[ var ] cpsM μα) →
             {k₂ : cpsvalue[ var ] (cpsT τ₁) →
                    cpsvalue[ var ] (cpsM μα) → cpsterm[ var ] (cpsT α)} →
             cpsSubst (λ x₁ → k x₁ x t) (CPSVar v) (k₂ x t)


  
  kSubst′′ : {var : cpstyp → Set}{τ₁ α β : typ} {μα μβ : trail}{μs : trails[ μβ ] μα} {τ : cpstyp} →
           (e : term[ var ∘ cpsT ] τ₁ ⟨ μs ⟩ α ⟨ μβ ⟩ β) →
           {v : var τ} →
           (k₁ : var τ →
                  cpsvalue[ var ] (cpsT τ₁) → cpsvalue[ var ] (cpsMs μs) → cpsterm[ var ] (cpsT α)) →
           {k₂ : cpsvalue[ var ] (cpsT τ₁) → cpsvalue[ var ] (cpsMs μs) → cpsterm[ var ] (cpsT α)} →
           {t₁ : cpsvalue[ var ] (cpsM μβ)} →
           --{t′ : cpsvalue[ var ] (cpsM μα)} →
           subst-cont k₁ (CPSVar v) k₂ →
           --schematicK′ k₁ →
           cpsSubst (λ x → cpsTerm e (k₁ x) t₁) (CPSVar v) (cpsTerm e k₂ t₁)
  kSubst′′ (Val x₁) k₁ x = x SubstV≠
  kSubst′′ (App e e₁) k₁ x = kSubst′′ e
                                 (λ x₁ →
                                    λ v₁ →
                                      cpsTerm e₁
                                      (λ v₂ t₂ →
                                         CPSApp
                                         (CPSApp (CPSApp (CPSVal v₁) (CPSVal v₂))
                                          (CPSVal
                                           (CPSFun
                                            (λ v₃ →
                                               CPSVal (CPSFun (λ t'' → k₁ x₁ (CPSVar v₃) (CPSVar t'')))))))
                                         (CPSVal t₂)))
                                 (λ {v₁} x₁ → kSubst′′ e₁
                                                  (λ x₂ →
                                                     λ v₂ t₂ →
                                                       CPSApp
                                                       (CPSApp (CPSApp (CPSVal (v₁ x₂)) (CPSVal v₂))
                                                        (CPSVal
                                                         (CPSFun
                                                          (λ v₃ →
                                                             CPSVal (CPSFun (λ t'' → k₁ x₂ (CPSVar v₃) (CPSVar t'')))))))
                                                       (CPSVal t₂))
                                                  (λ x₂ → sApp (sApp (sApp (sVal x₁) (sVal x₂))
                                                  (sVal (sFun (λ x₃ → sVal (sFun (λ x₄ → x SubstV≠)))))) Subst≠))
  kSubst′′ (Plus e e₁) k₁ x = kSubst′′ e
                                  (λ x₁ →
                                     λ v₁ →
                                       cpsTerm e₁
                                       (λ v₂ t₂ →
                                          CPSLet (CPSPlus (CPSVal v₁) (CPSVal v₂))
                                          (λ v₃ → k₁ x₁ (CPSVar v₃) t₂)))
                                  (λ {v₁} x₁ → kSubst′′ e₁
                                                   (λ x₂ →
                                                      λ v₂ t₂ →
                                                        CPSLet (CPSPlus (CPSVal (v₁ x₂)) (CPSVal v₂))
                                                        (λ v₃ → k₁ x₂ (CPSVar v₃) t₂))
                                                   (λ x₂ → sLet (λ x₃ → x SubstV≠)
                                                   (λ x₃ → sPlu (sVal x₁) (sVal x₂))))
  kSubst′′ (Control x₁ x₂ x₃ e) k₁ x = sLet (λ x₄ → Subst≠) (λ x₄ → sVal (sFun (λ x₅ →
                                      sVal (sFun (λ x₆ → sVal (sFun (λ x₇ → sLet (λ x₈ → x SubstV≠)
                                      (λ x₈ → Subst≠))))))))
  kSubst′′ (Prompt x₁ e) k₁ x = sLet (λ x₂ → x SubstV≠) (λ x₂ → Subst≠)
    

  kSubst : {var : cpstyp → Set}{τ₁ α β : typ} {μα μβ : trail}{μs : trails[ μβ ] μα} {τ : cpstyp} →
           (e : term[ var ∘ cpsT ] τ₁ ⟨ μs ⟩ α ⟨ μβ ⟩ β) →
           {v : cpsvalue[ var ] τ} →
           (k₁ : cpsvalue[ var ] τ →
                  cpsvalue[ var ] (cpsT τ₁) → cpsvalue[ var ] (cpsMs μs) → cpsterm[ var ] (cpsT α)) →
           --{k₂ : cpsvalue[ var ] (cpsT τ₁) → cpsvalue[ var ] (cpsM μα) → cpsterm[ var ] (cpsT α)} →
           {t₁ : cpsvalue[ var ] (cpsM μβ)} →
           --{t′ : cpsvalue[ var ] (cpsM μα)} →
           --subst-cont k₁ v k₂ →
           schematicK k₁ →
           cpsSubst (λ x → cpsTerm e (k₁ (CPSVar x)) t₁) v (cpsTerm e (k₁ v) t₁)

  kSubst (Val x₁) k₁ {t₁ = t₁} sch = sch (cpsV x₁) t₁
  kSubst (App e e₁) k₁ sch = kSubst e
    (λ x →
       λ v₁ →
         cpsTerm e₁
         (λ v₂ t₂ →
            CPSApp
            (CPSApp (CPSApp (CPSVal v₁) (CPSVal v₂))
             (CPSVal
              (CPSFun
               (λ v₃ → CPSVal (CPSFun (λ t'' → k₁ x (CPSVar v₃) (CPSVar t'')))))))
            (CPSVal t₂)))
    (λ x t →
    kSubst e₁
      (λ x₁ →
         λ v₂ t₂ →
           CPSApp
           (CPSApp (CPSApp (CPSVal x) (CPSVal v₂))
            (CPSVal
             (CPSFun
              (λ v₃ →
                 CPSVal (CPSFun (λ t'' → k₁ x₁ (CPSVar v₃) (CPSVar t'')))))))
           (CPSVal t₂))
      (λ x₁ t₂ → sApp (sApp Subst≠ (sVal (sFun (λ x₂ → sVal (sFun (λ x₃ → sch (CPSVar x₂) (CPSVar x₃)))))))
      Subst≠))
  kSubst (Plus e e₁) k₁ sch = kSubst e
                                (λ x →
                                   λ v₁ →
                                     cpsTerm e₁
                                     (λ v₂ t₂ →
                                        CPSLet (CPSPlus (CPSVal v₁) (CPSVal v₂))
                                        (λ v₃ → k₁ x (CPSVar v₃) t₂)))
                                (λ x t →
                                kSubst e₁
                                  (λ x₁ →
                                     λ v₂ t₂ →
                                       CPSLet (CPSPlus (CPSVal x) (CPSVal v₂))
                                       (λ v₃ → k₁ x₁ (CPSVar v₃) t₂))
                                  (λ x₁ t₂ → sLet (λ x₂ → sch (CPSVar x₂) t₂)
                                  (λ x₂ → Subst≠)))
  kSubst (Control x₁ x₂ x₃ e) k₁ sch = sLet (λ x → Subst≠) (λ x → sVal (sFun
                                      (λ x₄ → sVal (sFun (λ x₅ → sVal (sFun (λ x₆ → sLet (λ x₇ →
                                      sch (CPSVar x₄) (CPSVar x₇)) (λ x₇ → Subst≠))))))))
  kSubst (Prompt x₁ e) k₁ {t₁ = t₁} sch = sLet (λ x → sch (CPSVar x) t₁) λ x → Subst≠

  tSubst : {var : cpstyp → Set}{τ₁ α β : typ} {μα μβ : trail}{μs : trails[ μβ ] μα} →
           (e : term[ var ∘ cpsT ] τ₁ ⟨ μs ⟩ α ⟨ μβ ⟩ β) →
           {v : cpsvalue[ var ] (cpsM μβ)} →
           --(t₁ : var τ → cpsvalue[ var ] (cpsM μβ)) →
           {k : cpsvalue[ var ] (cpsT τ₁) → cpsvalue[ var ] (cpsMs μs) → cpsterm[ var ] (cpsT α)} →
           --(t₂ : cpsvalue[ var ] (cpsM μβ)) →
           --subst-trail {τ₁ = τ₁}{τ₂ = τ₂} t₁ v t₂ →
           schematicV′ k →
           cpsSubst (λ x → cpsTerm e k (CPSVar x)) v (cpsTerm e k v)

  tSubst (Val x) {v = v} sch = sch v (cpsV x)
  tSubst (App e e₁) sch = tSubst e (λ t v₂ → tSubst e₁ (λ t₁ v₃ → sApp Subst≠ (sVal sVar=)))
  tSubst (Plus e e₁) sch = tSubst e (λ t v₂ → tSubst e₁ (λ t₁ v₃ → sLet (λ x → sch t₁ (CPSVar x)) (λ x → Subst≠)))
  tSubst (Control x x₁ x₂ e) sch = sLet (λ x₃ → Subst≠) (λ x₃ → sVal
                                   (sFun (λ x₄ → sVal (sFun (λ x₅ → sVal (sFun (λ x₆ →
                                   sLet (λ x₇ → Subst≠) λ x₇ → sVal (sApd sVar= SubstV≠))))))))
  tSubst (Prompt x e) {v = v} sch = sLet (λ x₁ → sch v (CPSVar x₁)) λ x₁ → Subst≠


  ekSubst  : {var : cpstyp → Set} {τ τ₁ α β : typ} {μα μβ : trail}{μs : trails[ μβ ] μα} →
             {e₁ : (var ∘ cpsT) τ → term[ var ∘ cpsT ] τ₁ ⟨ μs ⟩ α ⟨ μβ ⟩ β} →
             {e₂ : term[ var ∘ cpsT ] τ₁ ⟨ μs ⟩ α ⟨ μβ ⟩ β} →
             {v : value[ var ∘ cpsT ] τ} →
             {k₁ : var (cpsT τ) → cpsvalue[ var ] (cpsT τ₁) →
              cpsvalue[ var ] (cpsMs μs) → cpsterm[ var ] (cpsT α)} →
             {k₂ : cpsvalue[ var ] (cpsT τ₁) →
              cpsvalue[ var ] (cpsMs μs) → cpsterm[ var ] (cpsT α)} →
             {t₁ : cpsvalue[ var ] (cpsM μβ)} →
             Subst e₁ v e₂ →
             subst-cont k₁ (cpsV v) k₂ →
             cpsSubst (λ y → cpsTerm (e₁ y) (k₁ y) t₁) (cpsV v)
                     (cpsTerm e₂ k₂ t₁)

  ekSubst (sVal x) eq = eq (eSubstV x)
  ekSubst (sApp sub₁ sub₂) eq = ekSubst sub₁ (λ m → ekSubst sub₂ (λ n → sApp (sApp (sApp (sVal m) (sVal n)) (sVal (sFun (λ x → sVal (sFun (λ x₁ → eq SubstV≠)))))) Subst≠))
  ekSubst (sPlu sub₁ sub₂) eq = ekSubst sub₁ (λ m → ekSubst sub₂ (λ n → sLet (λ x → eq SubstV≠) (λ x → sPlu (sVal m) (sVal n))))
  ekSubst (sCon e) eq = sLet (λ x → ekSubst (e x) (λ x₄ → sIdk x₄ SubstV≠)) λ x → sVal (sFun (λ x₄ → sVal (sFun λ x₁ → sVal (sFun (λ x₆ → sLet (λ x₇ → eq SubstV≠) (λ x₇ → Subst≠))))))
  ekSubst (sPro e) eq = sLet (λ v → eq SubstV≠) λ x₁ → ekSubst e (λ x₂ → sIdk x₂ SubstV≠)


-- ([e₁]′ @ k)[v/y] = [e₂]′ @ k
  -- ekSubst'  : {var : cpstyp → Set} {τ₁ τ α β : typ} {μα μβ : trail} →
  --             {e₁ : var (cpsT τ) →
  --                   term[ var ∘ cpsT ] τ₁ ⟨ μα ⟩ α ⟨ μβ ⟩ β} →
  --             {e₂ : term[ var ∘ cpsT ] τ₁ ⟨ μα ⟩ α ⟨ μβ ⟩ β} →
  --             {v : value[ var ∘ cpsT ] τ} →
  --             (k : cpsvalue[ var ] (cpsT τ₁) → cpsvalue[ var ] (cpsM μα) →
  --             cpsterm[ var ] (cpsT α)) →
  --             (t : cpsvalue[ var ] (cpsM μβ)) →
  --             Subst e₁ v e₂ →
  --             cpsSubst (λ x → cpsTerm (e₁ x) k t)
  --                     (cpsV v)
  --                     (cpsTerm e₂ k t)

  -- ekSubst' k t (sVal sub) = {!!}
  -- ekSubst' k t (sApp sub₁ sub₂) = {!!}
  -- ekSubst' k t (sPlu x x₁) = {!!}
  -- ekSubst' k t (sCon x) = {!!}
  -- ekSubst' k t (sPro x) = {!!}

  

-- schematic : {var : cpstyp → Set} {τ₁ α : typ}{μα : trail} →
--             (k : cpsvalue[ var ] (cpsT τ₁) →
--                  cpsvalue[ var ] (cpsM μα) → cpsterm[ var ] (cpsT α)) →
--             (t : cpsvalue[ var ] cpsM μα) → Set
-- schematic {var} {τ₁} k  t =
--   (v : cpsvalue[ var ] (cpsT τ₁)) →
--   cpsSubst (λ x → k (CPSVar x) t) v (k v t)

correctCont :  {var : cpstyp → Set} {τ₁ α β : typ} {μα μβ : trail}{μs : trails[ μβ ] μα} →
               (e : term[ var ∘ cpsT ] τ₁ ⟨ μs ⟩ α ⟨ μβ ⟩ β) →
               (k₁ : cpsvalue[ var ] (cpsT τ₁) → cpsvalue[ var ] (cpsMs μs) → cpsterm[ var ] (cpsT α)) →
               {k₂ : cpsvalue[ var ] (cpsT τ₁) → cpsvalue[ var ] (cpsMs μs) → cpsterm[ var ] (cpsT α)} →
               {t₂ : cpsvalue[ var ] (cpsM μβ)} →
               schematic  k₁ →
               --schematicV  k₂ →
               -- ((v : value[ var ∘ cpsT ] τ₁) →
               --  subst-cont k₁ v k₂) →
               ((v : value[ var ∘ cpsT ] τ₁) → (t : cpsvalue[ var ] (cpsMs μs)) →
                cpsreduce (k₁ (cpsV v) t) (k₂ (cpsV v) t)) →
               cpsreduce (cpsTerm e k₁ t₂) (cpsTerm e k₂ t₂)

correctCont (Val x₁) k₁ {k₂} {t₂ = t₂} sch₁ x = x x₁ t₂
correctCont (App e e₁) k₁ {k₂}  {t₂} sch₁ x = begin
 (cpsTerm e
       (λ v₁ →
          cpsTerm e₁
          (λ v₂ t₃ →
             CPSApp
             (CPSApp (CPSApp (CPSVal v₁) (CPSVal v₂))
              (CPSVal
               (CPSFun
                (λ v → CPSVal (CPSFun (λ t'' → k₁ (CPSVar v) (CPSVar t'')))))))
             (CPSVal t₃)))
       t₂)

  ⟶⟨ correctCont e
       (λ v₁ →
          cpsTerm e₁
          (λ v₂ t₃ →
             CPSApp
             (CPSApp (CPSApp (CPSVal v₁) (CPSVal v₂))
              (CPSVal
               (CPSFun
                (λ v → CPSVal (CPSFun (λ t'' → k₁ (CPSVar v) (CPSVar t'')))))))
             (CPSVal t₃)))
       {λ v₁ →
          cpsTerm e₁
          (λ v₂ t₃ →
             CPSApp
             (CPSApp (CPSApp (CPSVal v₁) (CPSVal v₂))
              (CPSVal
               (CPSFun
                (λ v → CPSVal (CPSFun (λ t'' → k₂ (CPSVar v) (CPSVar t'')))))))
             (CPSVal t₃))}
       (λ v t → kSubst e₁
                    (λ x₁ →
                       λ v₂ t₃ →
                         CPSApp
                         (CPSApp (CPSApp (CPSVal x₁) (CPSVal v₂))
                          (CPSVal
                           (CPSFun
                            (λ v₁ → CPSVal (CPSFun (λ t'' → k₁ (CPSVar v₁) (CPSVar t'')))))))
                         (CPSVal t₃))
                    (λ x₁ t₁ → sApp (sApp (sApp (sVal sVar=) Subst≠) Subst≠) Subst≠) )
                    (λ v t → correctCont e₁
                                 (λ v₂ t₃ →
                                    CPSApp
                                    (CPSApp (CPSApp (CPSVal (cpsV v)) (CPSVal v₂))
                                     (CPSVal
                                      (CPSFun
                                       (λ v₁ → CPSVal (CPSFun (λ t'' → k₁ (CPSVar v₁) (CPSVar t'')))))))
                                    (CPSVal t₃))
                                 {λ v₂ t₃ →
                                    CPSApp
                                    (CPSApp (CPSApp (CPSVal (cpsV v)) (CPSVal v₂))
                                     (CPSVal
                                      (CPSFun
                                       (λ v₁ → CPSVal (CPSFun (λ t'' → k₂ (CPSVar v₁) (CPSVar t'')))))))
                                    (CPSVal t₃)}
                                 (λ v₁ t₁ → sApp (sApp (sApp Subst≠ (sVal sVar=)) Subst≠) Subst≠)
                                 (λ v₁ t₁ → rApp₁ (rApp₂ (rFun (λ x₁ → rFun (λ x₂ → x (Var x₁) (CPSVar x₂)))))))  ⟩

  (cpsTerm e
       (λ v₁ →
          cpsTerm e₁
          (λ v₂ t₃ →
             CPSApp
             (CPSApp (CPSApp (CPSVal v₁) (CPSVal v₂))
              (CPSVal
               (CPSFun
                (λ v → CPSVal (CPSFun (λ t'' → k₂ (CPSVar v) (CPSVar t'')))))))
             (CPSVal t₃)))
       t₂)

  ∎
correctCont (Plus e e₁) k₁ {k₂} {t₂ = t₂} sch₁ x = begin
  (cpsTerm e
       (λ v₁ →
          cpsTerm e₁
          (λ v₂ t₃ →
             CPSLet (CPSPlus (CPSVal v₁) (CPSVal v₂)) (λ v → k₁ (CPSVar v) t₃)))
       t₂)
  ⟶⟨ correctCont e
       (λ v₁ →
          cpsTerm e₁
          (λ v₂ t₃ →
             CPSLet (CPSPlus (CPSVal v₁) (CPSVal v₂)) (λ v → k₁ (CPSVar v) t₃)))
       {λ v₁ →
          cpsTerm e₁
          (λ v₂ t₃ →
             CPSLet (CPSPlus (CPSVal v₁) (CPSVal v₂)) (λ v → k₂ (CPSVar v) t₃))}
       (λ v t → kSubst e₁
                    (λ x₁ →
                       λ v₂ t₃ →
                         CPSLet (CPSPlus (CPSVal x₁) (CPSVal v₂))
                         (λ v₁ → k₁ (CPSVar v₁) t₃))
                    (λ x₁ t₁ → sLet (λ x₂ → Subst≠) (λ x₂ → sPlu
                    (sVal sVar=) Subst≠)))
       (λ v t → correctCont e₁
                    (λ v₂ t₃ →
                       CPSLet (CPSPlus (CPSVal (cpsV v)) (CPSVal v₂))
                       (λ v₁ → k₁ (CPSVar v₁) t₃))
                    {λ v₂ t₃ →
                       CPSLet (CPSPlus (CPSVal (cpsV v)) (CPSVal v₂))
                       (λ v₁ → k₂ (CPSVar v₁) t₃)}
                    (λ v₁ t₁ → sLet (λ x₁ → Subst≠)
                    (λ x₁ → sPlu Subst≠ (sVal sVar=)))
                    (λ v₁ t₁ → rLet₂ (λ x₁ → x (Var x₁) t₁))) ⟩
  (cpsTerm e
       (λ v₁ →
          cpsTerm e₁
          (λ v₂ t₃ →
             CPSLet (CPSPlus (CPSVal v₁) (CPSVal v₂)) (λ v → k₂ (CPSVar v) t₃)))
       t₂)
  ∎
correctCont {μs = μs} (Control{μs₁ = μs₁} x₁ x₂ x₃ e) k₁ {k₂} {t₂ = t₂} sch₁ x = begin
  (cpsTerm {μs = μs} (Control{μs₁ = μs₁} x₁ x₂ x₃ e) k₁ t₂)
  ⟶⟨ rLet₁ (rFun (λ x₄ → rFun (λ x₅ → rFun (λ x₆ → rLet₂ (λ x₇ → x (Var x₄) (CPSVar x₇)))))) ⟩
  (cpsTerm {μs = μs} (Control{μs₁ = μs₁} x₁ x₂ x₃ e) k₂ t₂)
  ∎

correctCont (Prompt x₁ e) k₁ {k₂} {t₂ = t₂} sch₁ x = rLet₂ (λ x₂ → x (Var x₂) t₂)




mutual
  pSubstV≠ : {var : typ → Set} {τ₁ τ₂ : typ} →
             {t : value[ var ] τ₁ } →
             {v : value[ var ] τ₂ } →
             SubstVal (λ y → t) v t

  pSubstV≠ {t = Var x} = sVar≠
  pSubstV≠ {t = Num n} = sNum
  pSubstV≠ {t = Fun e₁} = sFun (λ x → pSubst≠)
  pSubst≠ : {var : typ → Set} {τ₁ τ₂ α β : typ}{μα μβ : trail}{μs : trails[ μβ ] μα} →
            {t : term[ var ] τ₁ ⟨ μs ⟩ α ⟨ μβ ⟩ β} →
            {v : value[ var ] τ₂ } →
            Subst (λ y → t) v t

  pSubst≠ {t = Val x} = sVal pSubstV≠
  pSubst≠ {t = App t t₁} = sApp pSubst≠ pSubst≠
  pSubst≠ {t = Plus t t₁} = sPlu pSubst≠ pSubst≠
  pSubst≠ {t = Control x x₁ x₂ e} = sCon (λ k → pSubst≠)
  pSubst≠ {t = Prompt x t} = sPro pSubst≠

subst-context : {var : typ → Set} {τ α τ₁ τ₂ α' : typ}{μα μ₁ μ₂ : trail}{μt : trails[ μ₂ ] μ₁} →
                (con : pcontext[ var , τ ⟨ []{μα} ⟩ α ⟨ μα ⟩ α ] τ₁ ⟨ μt ⟩ τ₂ ⟨ μ₂ ⟩ α' ) →
                (v : value[ var ] τ) →
                Subst (λ x → pcontext-plug con (Val (Var x))) v
                      (pcontext-plug con (Val v))

subst-context Hole v = sVal sVar=
subst-context (Frame (App₁ e₂) con) v = sApp (subst-context con v) pSubst≠
subst-context (Frame (App₂ v₁) con) v = sApp pSubst≠ (subst-context con v)
subst-context (Frame (Plus₁ e₂) con) v = sPlu (subst-context con v) pSubst≠
subst-context (Frame (Plus₂ v₁) con) v = sPlu pSubst≠ (subst-context con v)



-- control-lemma : ∀ {var : cpstyp → Set}{τ τ₁ τ₂ α β γ γ' t₁ t₂ α' : typ}
--               {μ₀ μ₁ μ₂ μᵢ μα μβ μα' : trail}
--               {μ[α]α : trails[ μα' ] μα'} → 
--               {μsᵢ : trails[ ∙ ] μᵢ} →
--               {μs₁ : trails[ μ₂ ] μ₁} →  
--               {μ[β]α : trails[ μβ ] μα} →
--               (p₁ : pcontext[ var ∘ cpsT , τ ⟨ μ[β]α ⟩ α ⟨ μβ ⟩ β ]
--                             τ₁ ⟨ μsᵢ ⟩ τ₂ ⟨ ∙ ⟩ β ) →
--               (p₂ : pcontext[ var ∘ cpsT , τ ⟨ [] ⟩ α' ⟨ μα' ⟩ α' ]
--                             τ₁ ⟨ μs₁ ⟩ τ₂ ⟨ μ₂ ⟩ α ) →
--               {id₀ : is-id-trails τ₁ τ₂ μsᵢ} →
--               (id : is-id-trails γ γ' μsᵢ) →
--               (c₁ : compatible (t₁ ⇒ t₂ , μ₁) μ₂ μ₂) →
--               (c₂ : compatible μβ μ₂ μα) →
--               same-pcontext p₁ p₂ →
--               (e : var (cpsT (τ ⇒ t₁ ⟨ μs₁ ⟩ t₂ ⟨ μ₂ ⟩ α)) →
--                    term[ var ∘ cpsT ] γ ⟨ μsᵢ ⟩ γ' ⟨ ∙ ⟩ β) →
--                --(k₁ : cpsvalue[ var ] cpsT t₁ → cpsvalue[ var ] cpsM μ₁ → cpsterm[ var ] cpsT t₂ ) →
--                (k₁ : cpsvalue[ var ] cpsT τ₁ → cpsvalue[ var ] cpsMs μsᵢ → cpsterm[ var ] cpsT τ₂) →
--                (tr : cpsvalue[ var ] cpsM ∙) →
--                (sch : schematic k₁) →
--                (sch' : schematicV′ k₁) →
--                cpsreduce (cpsTerm (pcontext-plug p₁ (Control id c₁ c₂ e)) k₁ tr)
--                (cpsTerm (App (Val (Fun (λ x → pcontext-plug p₂ (Val (Var x))))) (Control id c₁ refl e)) k₁ tr)

control-lemma : ∀ {var : cpstyp → Set}{τ τ₁ τ₂ τ₂' τ₅ α β γ γ' t₁ t₂ α' : typ}
              {μ₂ μ₁ μ₃ μᵢ μα μβ μα' μγ : trail}
              {μ[̇̇∙]α : trails[ ∙ ] μα}
              {μ[μ₂]μ₁ : trails[ μ₂ ] μ₁}→
              -- {μ[∙]μ₃ : trails[ ∙ ] μ₃} →
              {μ[β]μγ : trails[ μβ ] μγ} →
              {μ[α]μγ : trails[ μα ] μγ} →
              {μ[α]μ₃ : trails[ μα ] μ₃} →  
              {μ[β]α : trails[ μβ ] μα} →
              {μ[∙]μᵢ : trails[ ∙ ] μᵢ} →
              (p₁ : pcontext[ var ∘ cpsT , τ ⟨ μ[β]α ⟩ α ⟨ μβ ⟩ β ]
                            τ₁ ⟨ μ[β]μγ ⟩ τ₅ ⟨ μβ ⟩ β ) →
              (p₂ : pcontext[ var ∘ cpsT , τ ⟨ []{μα'} ⟩ τ₂' ⟨ μα' ⟩ τ₂' ]
                            τ₁ ⟨ μ[α]μγ ⟩ τ₅ ⟨ μα ⟩ α ) →
              --{id₀ : is-id-trails τ₁ τ₅ μ[∙]μ₃} →
              (id : is-id-trails γ γ' μ[∙]μᵢ) →
              (c₁ : compatible (t₁ ⇒ t₂ , μ₁) μ₂ μα) →
              (c₂ : compatible μβ μα μα) →
              same-pcontext p₁ p₂ →
              (e : var (cpsT (τ ⇒ t₁ ⟨ μ[μ₂]μ₁ ⟩ t₂ ⟨ μ₂ ⟩ α)) →
                   term[ var ∘ cpsT ] γ ⟨ μ[∙]μᵢ ⟩ γ' ⟨ ∙ ⟩ β) →
              (k₁ : cpsvalue[ var ] cpsT τ₁ → cpsvalue[ var ] cpsM μγ → cpsterm[ var ] cpsT τ₅) →
              (tr : cpsvalue[ var ] cpsM μβ) →
              (sch : schematic k₁) →
              (sch' : schematicV′ k₁) →
              cpsreduce
                (cpsTerm (pcontext-plug p₁ (Control{μs₁ = μ[μ₂]μ₁} id c₁ c₂ e)) k₁ tr)
                (cpsTerm{μs = μ[β]μγ}
                  (App{μ[γ]β = μ[β]α} (Val (Fun (λ x → pcontext-plug p₂ (Val (Var x)))))
                  (Control{μs₁ = μ[μ₂]μ₁} id c₁ c₂ e)) k₁ tr)

-- control-lemma Hole Hole id₁ c₁ c₂ same e k₁ tr sch sch' = {!!}
-- control-lemma (Frame f₁ p₁) (Frame f₂ p₂) id₁ c₁ c₂ same e k₁ tr sch sch' = {!!}
  

control-lemma Hole Hole id₁ c₁ c₂ x e k₁ tr sch sch' = {!!}
control-lemma (Frame (App₁ e₂) p₁') (Frame (App₁ .e₂) p₂') x₁ x₂ x₃
              (Frame {f₁ = (App₁ e₂)}{f₂ = (App₁ .e₂)} (App₁ .e₂) {c₁ = c₁}{c₂ = c₂} x₄) e k₁ t₁ sch sch' = begin

  (cpsTerm (pcontext-plug p₁' (Control x₁ x₂ x₃ e))
       (λ v₁ →
          cpsTerm e₂
          (λ v₂ t₄ →
             CPSApp
             (CPSApp (CPSApp (CPSVal v₁) (CPSVal v₂))
              (CPSVal
               (CPSFun
                (λ v → CPSVal (CPSFun (λ t'' → k₁ (CPSVar v) (CPSVar t'')))))))
             (CPSVal t₄)))
       t₁)

  ⟶⟨ {!control-lemma p₁' p₂'!} ⟩
  {!!}
  ⟶⟨ {!!} ⟩
  (CPSLet
       (CPSVal
        (CPSFun
         (λ v →
            CPSVal
            (CPSFun
             (λ k' →
                CPSVal
                (CPSFun
                 (λ t' →
                    CPSLet
                    (CPSVal (CPSAppend {!!} t₁ (CPSCons x₂ (CPSVar k') (CPSVar t'))))
                    (λ t'' →
                       CPSApp
                       (CPSApp
                        (CPSApp
                         (CPSVal
                          (CPSFun
                           (λ x →
                              CPSVal
                              (CPSFun
                               (λ k'' →
                                  CPSVal
                                  (CPSFun
                                   (λ t''' →
                                      cpsTerm (pcontext-plug p₂' (Val (Var x)))
                                      (λ v₁ →
                                         cpsTerm e₂
                                         (λ v₂ t₄ →
                                            CPSApp
                                            (CPSApp (CPSApp (CPSVal v₁) (CPSVal v₂))
                                             (CPSVal
                                              (CPSFun
                                               (λ v₃ →
                                                  CPSVal
                                                  (CPSFun
                                                   (λ t'''' →
                                                      CPSApp
                                                      (CPSApp (CPSVal (CPSVar k''))
                                                       (CPSVal (CPSVar v₃)))
                                                      (CPSVal (CPSVar t''''))))))))
                                            (CPSVal t₄)))
                                      (CPSVar t'''))))))))
                         (CPSVal (CPSVar v)))
                        (CPSVal
                         (CPSFun
                          (λ v₁ → CPSVal (CPSFun (λ t''' → k₁ (CPSVar v₁) (CPSVar t''')))))))
                       (CPSVal (CPSVar t''))))))))))
       (λ x' → cpsTerm (e x') (CPSIdk x₁) CPSId))

  ∎
control-lemma (Frame (App₂ v₁) p₁) (Frame f₁ p₂) id₁ c₁ c₂ x e k₁ tr sch sch' = {!!}
control-lemma (Frame (Plus₁ e₂) p₁) (Frame f₁ p₂) id₁ c₁ c₂ x e k₁ tr sch sch' = {!!}
control-lemma (Frame (Plus₂ v₁) p₁) (Frame f₁ p₂) id₁ c₁ c₂ x e k₁ tr sch sch' = {!!}
{-
control-lemma Hole Hole x₁ x₂ refl Hole e k₁ t₁ sch  sch' = {!!}
{-begin
  (CPSLet
       (CPSVal
        (CPSFun
         (λ v →
            CPSVal
            (CPSFun
             (λ k' →
                CPSVal
                (CPSFun
                 (λ t' →
                    CPSLet
                    (CPSVal (CPSAppend refl t₁
                      (CPSCons x₂ (CPSVar k')
                      (CPSVar t'))))
                    (λ t'' → k₁ (CPSVar v) (CPSVar t'')))))))))
       (λ x' → cpsTerm (e x') (CPSIdk x₁) CPSId))
  ≡⟨ refl ⟩
  CPSLet
    (CPSVal
     (CPSFun
      (λ z →
         CPSVal
         (CPSFun
          (λ z₁ →
             CPSVal
             (CPSFun
              (λ z₂ →
                 CPSLet
                 (CPSVal (CPSAppend refl t₁
                  (CPSCons x₂ (CPSVar z₁)
                   (CPSVar z₂))))
                 (λ z₃ → k₁ (CPSVar z) (CPSVar z₃)))))))))
    (λ x' → cpsTerm (e x') (CPSIdk x₁) CPSId)
  ⟵⟨ rLet₁ (rFun (λ x → rFun (λ x₄ → rFun (λ x₅ → rLet₂ (λ x₆ → rBeta (sch' (CPSVar x₆) (CPSVar x))))))) ⟩
  CPSLet
    (CPSVal
     (CPSFun
      (λ z →
         CPSVal
         (CPSFun
          (λ z₁ →
             CPSVal
             (CPSFun
              (λ z₂ →
                 CPSLet
                 (CPSVal (CPSAppend refl t₁
                  (CPSCons x₂ (CPSVar z₁)
                   (CPSVar z₂))))
                 (λ z₃ →
                    CPSApp (CPSVal (CPSFun (λ z₄ → k₁ (CPSVar z) (CPSVar z₄))))
                    (CPSVal (CPSVar z₃))))))))))
    (λ x' → cpsTerm (e x') (CPSIdk x₁) CPSId)
  ⟵⟨ rLet₁ (rFun (λ x → rFun (λ x₄ → rFun (λ x₅ → rLet₂ (λ x₆ → rApp₁ (rBeta
      (sVal (sFun (λ x₇ → sch (CPSVar x) (CPSVar x₇)))))))))) ⟩
  CPSLet
    (CPSVal
     (CPSFun
      (λ z →
         CPSVal
         (CPSFun
          (λ z₁ →
             CPSVal
             (CPSFun
              (λ z₂ →
                 CPSLet
                 (CPSVal (CPSAppend refl t₁
                  (CPSCons x₂ (CPSVar z₁)
                   (CPSVar z₂))))
                 (λ z₃ →
                    CPSApp
                    (CPSApp
                     (CPSVal
                      (CPSFun
                       (λ v₁ → CPSVal (CPSFun (λ t''' → k₁ (CPSVar v₁) (CPSVar t'''))))))
                     (CPSVal (CPSVar z)))
                    (CPSVal (CPSVar z₃))))))))))
    (λ x' → cpsTerm (e x') (CPSIdk x₁) CPSId)
  ⟵⟨ rLet₁ (rFun (λ x → rFun (λ x₄ → rFun (λ x₅ → rLet₂ (λ x₆ → rBeta
      (sApp Subst≠ (sVal sVar=))))))) ⟩
  CPSLet
    (CPSVal
     (CPSFun
      (λ z →
         CPSVal
         (CPSFun
          (λ z₁ →
             CPSVal
             (CPSFun
              (λ z₂ →
                 CPSLet
                 (CPSVal (CPSAppend refl t₁
                  (CPSCons x₂ (CPSVar z₁)
                   (CPSVar z₂))))
                 (λ z₃ →
                    CPSApp
                    (CPSVal
                     (CPSFun
                      (λ z₄ →
                         CPSApp
                         (CPSApp
                          (CPSVal
                           (CPSFun
                            (λ v₁ → CPSVal (CPSFun (λ t''' → k₁ (CPSVar v₁) (CPSVar t'''))))))
                          (CPSVal (CPSVar z)))
                         (CPSVal (CPSVar z₄)))))
                    (CPSVal (CPSVar z₃))))))))))
    (λ x' → cpsTerm (e x') (CPSIdk x₁) CPSId)
  ⟵⟨ rLet₁ (rFun (λ x → rFun (λ x₄ → rFun (λ x₅ → rLet₂ (λ x₆ → rApp₁ (rBeta
      (sVal (sFun (λ x₇ → sApp (sApp (sVal sVar=) Subst≠) Subst≠))))))))) ⟩
  CPSLet
    (CPSVal
     (CPSFun
      (λ z →
         CPSVal
         (CPSFun
          (λ z₁ →
             CPSVal
             (CPSFun
              (λ z₂ →
                 CPSLet
                 (CPSVal (CPSAppend refl t₁
                  (CPSCons x₂ (CPSVar z₁)
                   (CPSVar z₂))))
                 (λ z₃ →
                    CPSApp
                    (CPSApp
                     (CPSVal
                      (CPSFun
                       (λ z₄ →
                          CPSVal
                          (CPSFun
                           (λ z₅ →
                              CPSApp (CPSApp (CPSVal (CPSVar z₄)) (CPSVal (CPSVar z)))
                              (CPSVal (CPSVar z₅)))))))
                     (CPSVal
                      (CPSFun
                       (λ v₁ → CPSVal (CPSFun (λ t''' → k₁ (CPSVar v₁) (CPSVar t''')))))))
                    (CPSVal (CPSVar z₃))))))))))
    (λ x' → cpsTerm (e x') (CPSIdk x₁) CPSId)
  ⟵⟨ rLet₁ (rFun (λ x → rFun (λ x₄ → rFun (λ x₅ → rLet₂ (λ x₆ → rApp₁ (rApp₁ (rBeta
      (sVal (sFun (λ x₇ → sVal (sFun (λ x₈ → sApp (sApp Subst≠ (sVal sVar=)) Subst≠)))))))))))) ⟩
  (CPSLet
       (CPSVal
        (CPSFun
         (λ v →
            CPSVal
            (CPSFun
             (λ k' →
                CPSVal
                (CPSFun
                 (λ t' →
                    CPSLet
                    (CPSVal (CPSAppend refl t₁
                     (CPSCons x₂ (CPSVar k')
                      (CPSVar t'))))
                    (λ t'' →
                       CPSApp
                       (CPSApp
                        (CPSApp
                         (CPSVal
                          (CPSFun
                           (λ x →
                              CPSVal
                              (CPSFun
                               (λ k'' →
                                  CPSVal
                                  (CPSFun
                                   (λ t''' →
                                      CPSApp (CPSApp (CPSVal (CPSVar k'')) (CPSVal (CPSVar x)))
                                      (CPSVal (CPSVar t''')))))))))
                         (CPSVal (CPSVar v)))
                        (CPSVal
                         (CPSFun
                          (λ v₁ → CPSVal (CPSFun (λ t''' → k₁ (CPSVar v₁) (CPSVar t''')))))))
                       (CPSVal (CPSVar t''))))))))))
       (λ x' → cpsTerm (e x') (CPSIdk x₁) CPSId))
  ∎ -}
-- cpsreduce (cpsTerm (pcontext-plug p₁ (Control x₁ x₂ x₃ e)) k₁ tr)
--                (cpsTerm (App (Val (Fun (λ x → pcontext-plug p₃ (Val (Var x))))) (Control x₁ x₂ refl e)) k₁ tr)
control-lemma  (Frame (App₁ e₂) p₁') (Frame (App₁ .e₂) p₃') x₁ x₂ x₃
              (Frame {f₁ = (App₁ e₂)}{f₂ = (App₁ .e₂)} (App₁ .e₂) {c₁ = c₁}{c₂ = c₂} x₄) e k₁ t₁ sch sch' = begin

  (cpsTerm (pcontext-plug p₁' (Control x₁ x₂ x₃ e))
       (λ v₁ →
          cpsTerm e₂
          (λ v₂ t₄ →
             CPSApp
             (CPSApp (CPSApp (CPSVal v₁) (CPSVal v₂))
              (CPSVal
               (CPSFun
                (λ v → CPSVal (CPSFun (λ t'' → k₁ (CPSVar v) (CPSVar t'')))))))
             (CPSVal t₄)))
       t₁)

  ⟶⟨ {!control-lemma p₁' p₃'!} ⟩
  {!!}
  ⟶⟨ {!!} ⟩
  (CPSLet
       (CPSVal
        (CPSFun
         (λ v →
            CPSVal
            (CPSFun
             (λ k' →
                CPSVal
                (CPSFun
                 (λ t' →
                    CPSLet
                    (CPSVal (CPSAppend refl t₁ (CPSCons x₂ (CPSVar k') (CPSVar t'))))
                    (λ t'' →
                       CPSApp
                       (CPSApp
                        (CPSApp
                         (CPSVal
                          (CPSFun
                           (λ x →
                              CPSVal
                              (CPSFun
                               (λ k'' →
                                  CPSVal
                                  (CPSFun
                                   (λ t''' →
                                      cpsTerm (pcontext-plug p₃' (Val (Var x)))
                                      (λ v₁ →
                                         cpsTerm e₂
                                         (λ v₂ t₄ →
                                            CPSApp
                                            (CPSApp (CPSApp (CPSVal v₁) (CPSVal v₂))
                                             (CPSVal
                                              (CPSFun
                                               (λ v₃ →
                                                  CPSVal
                                                  (CPSFun
                                                   (λ t'''' →
                                                      CPSApp
                                                      (CPSApp (CPSVal (CPSVar k''))
                                                       (CPSVal (CPSVar v₃)))
                                                      (CPSVal (CPSVar t''''))))))))
                                            (CPSVal t₄)))
                                      (CPSVar t'''))))))))
                         (CPSVal (CPSVar v)))
                        (CPSVal
                         (CPSFun
                          (λ v₁ → CPSVal (CPSFun (λ t''' → k₁ (CPSVar v₁) (CPSVar t''')))))))
                       (CPSVal (CPSVar t''))))))))))
       (λ x' → cpsTerm (e x') (CPSIdk x₁) CPSId))

  ∎
{-begin

  (cpsTerm (pcontext-plug p₁' (Control x₁ x₂ x₃ e))
       (λ v₂ →
          cpsTerm e₂
          (λ v₃ t₄ →
             CPSApp
             (CPSApp (CPSApp (CPSVal v₂) (CPSVal v₃))
              (CPSVal
               (CPSFun
                (λ v → CPSVal (CPSFun (λ t'' → k₁ (CPSVar v) (CPSVar t'')))))))
             (CPSVal t₄)))
       t₁)

  ⟶⟨ control-lemma p₁' {!!} x₁ ? x₃ {!!} ?
       (λ v₂ →
          cpsTerm e₂
          (λ v₃ t₄ →
             CPSApp
             (CPSApp (CPSApp (CPSVal v₂) (CPSVal v₃))
              (CPSVal
               (CPSFun
                (λ v → CPSVal (CPSFun (λ t'' → k₁ (CPSVar v) (CPSVar t'')))))))
             (CPSVal t₄)))
       t₁ (λ v t → kSubst e₂
                          (λ x →
                             λ v₃ t₄ →
                               CPSApp
                               (CPSApp (CPSApp (CPSVal x) (CPSVal v₃))
                                (CPSVal
                                 (CPSFun
                                  (λ v₂ → CPSVal (CPSFun (λ t'' → k₁ (CPSVar v₂) (CPSVar t'')))))))
                               (CPSVal t₄))
                          (λ x t₄ → sApp (sApp (sApp (sVal sVar=) Subst≠) Subst≠) Subst≠))
                          (λ t v₂ → tSubst e₂ (λ t₄ v₃ → sApp Subst≠ (sVal sVar=))) ⟩
  CPSLet
    (CPSVal
     (CPSFun
      (λ z →
         CPSVal
         (CPSFun
          (λ z₁ →
             CPSVal
             (CPSFun
              (λ z₂ →
                 CPSLet
                 (CPSVal (CPSAppend refl t₁
                  (CPSCons x₂ (CPSVar z₁)
                   (CPSVar z₂))))
                 (λ t'' →
                    CPSApp
                    (CPSApp
                     (CPSApp
                      (CPSVal (cpsV (Fun (λ x → pcontext-plug p₃' (Val (Var x))))))
                      (CPSVal (CPSVar z)))
                     (CPSVal
                      (CPSFun
                       (λ v →
                          CPSVal
                          (CPSFun
                           (λ t''' →
                              cpsTerm e₂
                              (λ v₃ t₄ →
                                 CPSApp
                                 (CPSApp (CPSApp (CPSVal (CPSVar v)) (CPSVal v₃))
                                  (CPSVal
                                   (CPSFun
                                    (λ v₂ →
                                       CPSVal (CPSFun (λ t'''' → k₁ (CPSVar v₂) (CPSVar t'''')))))))
                                 (CPSVal t₄))
                              (CPSVar t''')))))))
                    (CPSVal (CPSVar t''))))))))))
    (λ x' → cpsTerm (e x') (CPSIdk x₁) CPSId)
  ⟶⟨ rLet₁ (rFun (λ x → rFun (λ x₅ → rFun (λ x₆ → rLet₂ (λ x₇ → rApp₁ (rApp₁ (rBeta
      (sVal (sFun (λ x₈ → sVal (sFun (λ x₉ → eSubst (subst-context p₃' (Var x)) (λ x₁₀ →
      sApp (sApp Subst≠ (sVal x₁₀)) Subst≠))))))))))))) ⟩
  CPSLet
    (CPSVal
     (CPSFun
      (λ z →
         CPSVal
         (CPSFun
          (λ z₁ →
             CPSVal
             (CPSFun
              (λ z₂ →
                 CPSLet
                 (CPSVal (CPSAppend refl t₁
                  (CPSCons x₂ (CPSVar z₁)
                   (CPSVar z₂))))
                 (λ z₃ →
                    CPSApp
                    (CPSApp
                     (CPSVal
                      (CPSFun
                       (λ z₄ →
                          CPSVal
                          (CPSFun
                           (λ z₅ →
                              cpsTerm (pcontext-plug p₃' (Val (Var z)))
                              (λ v t'' →
                                 CPSApp (CPSApp (CPSVal (CPSVar z₄)) (CPSVal v)) (CPSVal t''))
                              (CPSVar z₅))))))
                     (CPSVal
                      (CPSFun
                       (λ v →
                          CPSVal
                          (CPSFun
                           (λ t''' →
                              cpsTerm e₂
                              (λ v₃ t₄ →
                                 CPSApp
                                 (CPSApp (CPSApp (CPSVal (CPSVar v)) (CPSVal v₃))
                                  (CPSVal
                                   (CPSFun
                                    (λ v₂ →
                                       CPSVal (CPSFun (λ t'''' → k₁ (CPSVar v₂) (CPSVar t'''')))))))
                                 (CPSVal t₄))
                              (CPSVar t''')))))))
                    (CPSVal (CPSVar z₃))))))))))
    (λ x' → cpsTerm (e x') (CPSIdk x₁) CPSId)
  ⟶⟨ rLet₁ (rFun (λ x → rFun (λ x₅ → rFun (λ x₆ → rLet₂ (λ x₇ → rApp₁ (rBeta (sVal (sFun (λ x₈ →
      kSubst (pcontext-plug p₃' (Val (Var x)))
        (λ y →
           λ v t'' → CPSApp (CPSApp (CPSVal y) (CPSVal v)) (CPSVal t''))
        (λ x₉ t → sApp (sApp (sVal sVar=) Subst≠) Subst≠)))))))))) ⟩
  CPSLet
    (CPSVal
     (CPSFun
      (λ z →
         CPSVal
         (CPSFun
          (λ z₁ →
             CPSVal
             (CPSFun
              (λ z₂ →
                 CPSLet
                 (CPSVal (CPSAppend refl t₁
                  (CPSCons x₂ (CPSVar z₁)
                   (CPSVar z₂))))
                 (λ z₃ →
                    CPSApp
                    (CPSVal
                     (CPSFun
                      (λ z₄ →
                         cpsTerm (pcontext-plug p₃' (Val (Var z)))
                         (λ v t'' →
                            CPSApp
                            (CPSApp
                             (CPSVal
                              (CPSFun
                               (λ v₂ →
                                  CPSVal
                                  (CPSFun
                                   (λ t''' →
                                      cpsTerm e₂
                                      (λ v₃ t₄ →
                                         CPSApp
                                         (CPSApp (CPSApp (CPSVal (CPSVar v₂)) (CPSVal v₃))
                                          (CPSVal
                                           (CPSFun
                                            (λ v₄ →
                                               CPSVal
                                               (CPSFun (λ t'''' → k₁ (CPSVar v₄) (CPSVar t'''')))))))
                                         (CPSVal t₄))
                                      (CPSVar t'''))))))
                             (CPSVal v))
                            (CPSVal t''))
                         (CPSVar z₄))))
                    (CPSVal (CPSVar z₃))))))))))
    (λ x' → cpsTerm (e x') (CPSIdk x₁) CPSId)
  ⟶⟨ rLet₁ (rFun (λ x → rFun (λ x₅ → rFun (λ x₆ → rLet₂ (λ x₇ → rBeta
      (tSubst (pcontext-plug p₃' (Val (Var x))) (λ t v₂ → sApp Subst≠ (sVal sVar=)))))))) ⟩
  CPSLet
    (CPSVal
     (CPSFun
      (λ z →
         CPSVal
         (CPSFun
          (λ z₁ →
             CPSVal
             (CPSFun
              (λ z₂ →
                 CPSLet
                 (CPSVal (CPSAppend refl t₁
                  (CPSCons x₂ (CPSVar z₁)
                   (CPSVar z₂))))
                 (λ z₃ →
                    cpsTerm (pcontext-plug p₃' (Val (Var z)))
                    (λ v t'' →
                       CPSApp
                       (CPSApp
                        (CPSVal
                         (CPSFun
                          (λ v₂ →
                             CPSVal
                             (CPSFun
                              (λ t''' →
                                 cpsTerm e₂
                                 (λ v₃ t₄ →
                                    CPSApp
                                    (CPSApp (CPSApp (CPSVal (CPSVar v₂)) (CPSVal v₃))
                                     (CPSVal
                                      (CPSFun
                                       (λ v₄ →
                                          CPSVal (CPSFun (λ t'''' → k₁ (CPSVar v₄) (CPSVar t'''')))))))
                                    (CPSVal t₄))
                                 (CPSVar t'''))))))
                        (CPSVal v))
                       (CPSVal t''))
                    (CPSVar z₃)))))))))
    (λ x' → cpsTerm (e x') (CPSIdk x₁) CPSId)
  ⟶⟨ rLet₁ (rFun (λ x → rFun (λ x₅ → rFun (λ x₆ → rLet₂ (λ x₇ → correctCont (pcontext-plug p₃' (Val (Var x)))
                                                                          (λ v t'' →
                                                                             CPSApp
                                                                             (CPSApp
                                                                              (CPSVal
                                                                               (CPSFun
                                                                                (λ v₂ →
                                                                                   CPSVal
                                                                                   (CPSFun
                                                                                    (λ t''' →
                                                                                       cpsTerm e₂
                                                                                       (λ v₃ t₄ →
                                                                                          CPSApp
                                                                                          (CPSApp (CPSApp (CPSVal (CPSVar v₂)) (CPSVal v₃))
                                                                                           (CPSVal
                                                                                            (CPSFun
                                                                                             (λ v₄ →
                                                                                                CPSVal (CPSFun (λ t'''' → k₁ (CPSVar v₄) (CPSVar t'''')))))))
                                                                                          (CPSVal t₄))
                                                                                       (CPSVar t'''))))))
                                                                              (CPSVal v))
                                                                             (CPSVal t''))
                                                               {k₂ = (λ v t'' → (CPSApp (CPSVal (CPSFun (λ t''' →
                                               
                                                                                       cpsTerm e₂
                                                                                       (λ v₃ t₄ →
                                                                                          CPSApp
                                                                                          (CPSApp (CPSApp (CPSVal (v)) (CPSVal v₃))
                                                                                           (CPSVal
                                                                                            (CPSFun
                                                                                             (λ v₄ →
                                                                                                CPSVal (CPSFun (λ t'''' → k₁ (CPSVar v₄) (CPSVar t'''')))))))
                                                                                          (CPSVal t₄))
                                                                                       (CPSVar t'''))))(CPSVal t'')))}
                                                                          (λ v t → sApp (sApp Subst≠ (sVal sVar=)) Subst≠) λ v t →
                                                                          rApp₁ (rBeta (sVal (sFun (λ x₈ →
                                                                          kSubst e₂
                                                                            (λ y →
                                                                               λ v₃ t₄ →
                                                                                 CPSApp
                                                                                 (CPSApp (CPSApp (CPSVal y) (CPSVal v₃))
                                                                                  (CPSVal
                                                                                   (CPSFun
                                                                                    (λ v₄ →
                                                                                       CPSVal (CPSFun (λ t'''' → k₁ (CPSVar v₄) (CPSVar t'''')))))))
                                                                                 (CPSVal t₄))
                                                                            (λ x₉ t₄ → sApp (sApp (sApp (sVal sVar=) Subst≠) Subst≠) Subst≠)))))))))) ⟩
  CPSLet
    (CPSVal
     (CPSFun
      (λ z →
         CPSVal
         (CPSFun
          (λ z₁ →
             CPSVal
             (CPSFun
              (λ z₂ →
                 CPSLet
                 (CPSVal (CPSAppend refl t₁
                  (CPSCons x₂ (CPSVar z₁)
                   (CPSVar z₂))))
                 (λ z₃ →
                    cpsTerm (pcontext-plug p₃' (Val (Var z)))
                    (λ v t'' →
                       CPSApp
                       (CPSVal
                        (CPSFun
                         (λ t''' →
                            cpsTerm e₂
                            (λ v₃ t₄ →
                               CPSApp
                               (CPSApp (CPSApp (CPSVal v) (CPSVal v₃))
                                (CPSVal
                                 (CPSFun
                                  (λ v₄ →
                                     CPSVal (CPSFun (λ t'''' → k₁ (CPSVar v₄) (CPSVar t'''')))))))
                               (CPSVal t₄))
                            (CPSVar t'''))))
                       (CPSVal t''))
                    (CPSVar z₃)))))))))
    (λ x' → cpsTerm (e x') (CPSIdk x₁) CPSId)
  ⟶⟨ rLet₁ (rFun (λ x → rFun (λ x₅ → rFun (λ x₆ → rLet₂ (λ x₇ →
      correctCont (pcontext-plug p₃' (Val (Var x)))
        (λ v t'' →
           CPSApp
           (CPSVal
            (CPSFun
             (λ t''' →
                cpsTerm e₂
                (λ v₃ t₄ →
                   CPSApp
                   (CPSApp (CPSApp (CPSVal v) (CPSVal v₃))
                    (CPSVal
                     (CPSFun
                      (λ v₄ →
                         CPSVal (CPSFun (λ t'''' → k₁ (CPSVar v₄) (CPSVar t'''')))))))
                   (CPSVal t₄))
                (CPSVar t'''))))
           (CPSVal t''))
           {k₂ = (λ v t'' →
               cpsTerm e₂
               (λ v₃ t₄ →
                  CPSApp
                  (CPSApp (CPSApp (CPSVal v) (CPSVal v₃))
                   (CPSVal
                    (CPSFun
                     (λ v₄ →
                        CPSVal (CPSFun (λ t'''' → k₁ (CPSVar v₄) (CPSVar t'''')))))))
                  (CPSVal t₄))
               (t''))}
        (λ v t → sApp (sVal (sFun (λ x₈ → kSubst e₂
                                                (λ y →
                                                   λ v₃ t₄ →
                                                     CPSApp
                                                     (CPSApp (CPSApp (CPSVal y) (CPSVal v₃))
                                                      (CPSVal
                                                       (CPSFun
                                                        (λ v₄ →
                                                           CPSVal (CPSFun (λ t'''' → k₁ (CPSVar v₄) (CPSVar t'''')))))))
                                                     (CPSVal t₄))
                                                (λ x₉ t₄ → sApp (sApp (sApp (sVal sVar=) Subst≠) Subst≠) Subst≠)))) Subst≠)
                                                λ v t → rBeta (tSubst e₂ (λ t₄ v₂ → sApp Subst≠ (sVal sVar=)))))))) ⟩
  CPSLet
    (CPSVal
     (CPSFun
      (λ z →
         CPSVal
         (CPSFun
          (λ z₁ →
             CPSVal
             (CPSFun
              (λ z₂ →
                 CPSLet
                 (CPSVal (CPSAppend refl t₁
                  (CPSCons x₂ (CPSVar z₁)
                   (CPSVar z₂))))
                 (λ z₃ →
                    cpsTerm (pcontext-plug p₃' (Val (Var z)))
                    (λ v t'' →
                       cpsTerm e₂
                       (λ v₃ t₄ →
                          CPSApp
                          (CPSApp (CPSApp (CPSVal v) (CPSVal v₃))
                           (CPSVal
                            (CPSFun
                             (λ v₄ →
                                CPSVal (CPSFun (λ t'''' → k₁ (CPSVar v₄) (CPSVar t'''')))))))
                          (CPSVal t₄))
                       t'')
                    (CPSVar z₃)))))))))
    (λ x' → cpsTerm (e x') (CPSIdk x₁) CPSId)
  ⟵⟨ rLet₁ (rFun (λ x → rFun (λ x₅ → rFun (λ x₆ → rLet₂ (λ x₇ →
      correctCont (pcontext-plug p₃' (Val (Var x)))
        (λ v t'' →
           CPSApp
           (CPSVal
            (CPSFun
             (λ t''' →
                cpsTerm e₂
                (λ v₃ t₄ →
                   CPSApp
                   (CPSApp (CPSApp (CPSVal v) (CPSVal v₃))
                    (CPSVal
                     (CPSFun
                      (λ v₄ →
                         CPSVal (CPSFun (λ t'''' → k₁ (CPSVar v₄) (CPSVar t'''')))))))
                   (CPSVal t₄))
                (CPSVar t'''))))
           (CPSVal t''))
           {k₂ = (λ v t'' →
          cpsTerm e₂
          (λ v₃ t₄ →
             CPSApp
             (CPSApp (CPSApp (CPSVal v) (CPSVal v₃))
              (CPSVal
               (CPSFun
                (λ v₄ →
                   CPSVal (CPSFun (λ t'''' → k₁ (CPSVar v₄) (CPSVar t'''')))))))
             (CPSVal t₄))
          t'')}
        (λ v t → sApp (sVal (sFun (λ x₈ → kSubst e₂
                                                (λ y →
                                                   λ v₃ t₄ →
                                                     CPSApp
                                                     (CPSApp (CPSApp (CPSVal y) (CPSVal v₃))
                                                      (CPSVal
                                                       (CPSFun
                                                        (λ v₄ →
                                                           CPSVal (CPSFun (λ t'''' → k₁ (CPSVar v₄) (CPSVar t'''')))))))
                                                     (CPSVal t₄))
                                                (λ x₉ t₄ → sApp (sApp (sApp (sVal sVar=) Subst≠) Subst≠) Subst≠)))) Subst≠)
                                                λ v t → rBeta (tSubst e₂ (λ t₄ v₂ → sApp Subst≠ (sVal sVar=)))))))) ⟩
  CPSLet
    (CPSVal
     (CPSFun
      (λ z →
         CPSVal
         (CPSFun
          (λ z₁ →
             CPSVal
             (CPSFun
              (λ z₂ →
                 CPSLet
                 (CPSVal (CPSAppend refl t₁
                  (CPSCons x₂ (CPSVar z₁)
                   (CPSVar z₂))))
                 (λ z₃ →
                    cpsTerm (pcontext-plug p₃' (Val (Var z)))
                    (λ v t'' →
                       CPSApp
                       (CPSVal
                        (CPSFun
                         (λ t''' →
                            cpsTerm e₂
                            (λ v₃ t₄ →
                               CPSApp
                               (CPSApp (CPSApp (CPSVal v) (CPSVal v₃))
                                (CPSVal
                                 (CPSFun
                                  (λ v₄ →
                                     CPSVal (CPSFun (λ t'''' → k₁ (CPSVar v₄) (CPSVar t'''')))))))
                               (CPSVal t₄))
                            (CPSVar t'''))))
                       (CPSVal t''))
                    (CPSVar z₃)))))))))
    (λ x' → cpsTerm (e x') (CPSIdk x₁) CPSId)
  ⟵⟨ rLet₁ (rFun (λ x → rFun (λ x₅ → rFun (λ x₆ → rLet₂ (λ x₇ →
      correctCont (pcontext-plug p₃' (Val (Var x)))
        (λ v₂ →
           cpsTerm e₂
           (λ v₃ t₄ →
              CPSApp
              (CPSApp (CPSApp (CPSVal v₂) (CPSVal v₃))
               (CPSVal
                (CPSFun
                 (λ v₄ →
                    CPSVal
                    (CPSFun
                     (λ t'''' →
                        CPSApp (CPSVal (CPSFun (λ t''' → k₁ (CPSVar v₄) (CPSVar t'''))))
                        (CPSVal (CPSVar t''''))))))))
              (CPSVal t₄)))
              {k₂ = (λ v t'' →
                       CPSApp
                       (CPSVal
                        (CPSFun
                         (λ t''' →
                            cpsTerm e₂
                            (λ v₃ t₄ →
                               CPSApp
                               (CPSApp (CPSApp (CPSVal v) (CPSVal v₃))
                                (CPSVal
                                 (CPSFun
                                  (λ v₄ →
                                     CPSVal (CPSFun (λ t'''' → k₁ (CPSVar v₄) (CPSVar t'''')))))))
                               (CPSVal t₄))
                            (CPSVar t'''))))
                       (CPSVal t''))}
        (λ v t → kSubst e₂
                     (λ x₈ →
                        λ v₃ t₄ →
                          CPSApp
                          (CPSApp (CPSApp (CPSVal x₈) (CPSVal v₃))
                           (CPSVal
                            (CPSFun
                             (λ v₄ →
                                CPSVal
                                (CPSFun
                                 (λ t'''' →
                                    CPSApp (CPSVal (CPSFun (λ t''' → k₁ (CPSVar v₄) (CPSVar t'''))))
                                    (CPSVal (CPSVar t''''))))))))
                          (CPSVal t₄))
                     (λ x₈ t₄ → sApp (sApp (sApp (sVal sVar=) Subst≠) Subst≠) Subst≠))
        λ v t → (begin (cpsTerm e₂
       (λ v₃ t₄ →
          CPSApp
          (CPSApp (CPSApp (CPSVal (cpsV v)) (CPSVal v₃))
           (CPSVal
            (CPSFun
             (λ v₄ →
                CPSVal
                (CPSFun
                 (λ t'''' →
                    CPSApp (CPSVal (CPSFun (λ t''' → k₁ (CPSVar v₄) (CPSVar t'''))))
                    (CPSVal (CPSVar t''''))))))))
          (CPSVal t₄))
       t)
       ⟶⟨ correctCont e₂
            (λ v₃ t₄ →
               CPSApp
               (CPSApp (CPSApp (CPSVal (cpsV v)) (CPSVal v₃))
                (CPSVal
                 (CPSFun
                  (λ v₄ →
                     CPSVal
                     (CPSFun
                      (λ t'''' →
                         CPSApp (CPSVal (CPSFun (λ t''' → k₁ (CPSVar v₄) (CPSVar t'''))))
                         (CPSVal (CPSVar t''''))))))))
               (CPSVal t₄))
               {k₂ = (λ z z₁ →
          CPSApp
          (CPSApp (CPSApp (CPSVal (cpsV v)) (CPSVal z))
           (CPSVal
            (CPSFun
             (λ v₄ →
                CPSVal (CPSFun (λ t'''' → k₁ (CPSVar v₄) (CPSVar t'''')))))))
          (CPSVal z₁))}
            (λ v₂ t₄ → sApp (sApp (sApp Subst≠ (sVal sVar=)) Subst≠) Subst≠)
            (λ v₂ t₄ → rApp₁ (rApp₂ (rFun (λ x₈ → rFun (λ x₉ → rBeta (sch' (CPSVar x₉) (CPSVar x₈))))))) ⟩
       cpsTerm e₂
         (λ z z₁ →
            CPSApp
            (CPSApp (CPSApp (CPSVal (cpsV v)) (CPSVal z))
             (CPSVal
              (CPSFun
               (λ v₄ →
                  CPSVal (CPSFun (λ t'''' → k₁ (CPSVar v₄) (CPSVar t'''')))))))
            (CPSVal z₁))
         t
       ⟵⟨ rBeta (tSubst e₂ (λ t₄ v₂ → sApp Subst≠ (sVal sVar=))) ⟩
       (CPSApp
       (CPSVal
        (CPSFun
         (λ t''' →
            cpsTerm e₂
            (λ v₃ t₄ →
               CPSApp
               (CPSApp (CPSApp (CPSVal (cpsV v)) (CPSVal v₃))
                (CPSVal
                 (CPSFun
                  (λ v₄ →
                     CPSVal (CPSFun (λ t'''' → k₁ (CPSVar v₄) (CPSVar t'''')))))))
               (CPSVal t₄))
            (CPSVar t'''))))
       (CPSVal t))
       ∎)))))) ⟩ 
 CPSLet
   (CPSVal
    (CPSFun
     (λ z →
        CPSVal
        (CPSFun
         (λ z₁ →
            CPSVal
            (CPSFun
             (λ z₂ →
                CPSLet
                (CPSVal (CPSAppend refl t₁
                  (CPSCons x₂ (CPSVar z₁)
                   (CPSVar z₂))))
                (λ z₃ →
                   cpsTerm (pcontext-plug p₃' (Val (Var z)))
                   (λ v₂ →
                      cpsTerm e₂
                      (λ v₃ t₄ →
                         CPSApp
                         (CPSApp (CPSApp (CPSVal v₂) (CPSVal v₃))
                          (CPSVal
                           (CPSFun
                            (λ v₄ →
                               CPSVal
                               (CPSFun
                                (λ t'''' →
                                   CPSApp (CPSVal (CPSFun (λ t''' → k₁ (CPSVar v₄) (CPSVar t'''))))
                                   (CPSVal (CPSVar t''''))))))))
                         (CPSVal t₄)))
                   (CPSVar z₃)))))))))
   (λ x' → cpsTerm (e x') (CPSIdk x₁) CPSId)
  ⟵⟨ rLet₁ (rFun (λ x → rFun (λ x₅ → rFun (λ x₆ → rLet₂ (λ x₇ → correctCont (pcontext-plug p₃' (Val (Var x)))
                                                                          (λ v₂ →
                                                                             cpsTerm e₂
                                                                             (λ v₃ t₄ →
                                                                                CPSApp
                                                                                (CPSApp (CPSApp (CPSVal v₂) (CPSVal v₃))
                                                                                 (CPSVal
                                                                                  (CPSFun
                                                                                   (λ v₄ →
                                                                                      CPSVal
                                                                                      (CPSFun
                                                                                       (λ t'''' →
                                                                                          CPSApp
                                                                                          (CPSApp
                                                                                           (CPSVal
                                                                                            (CPSFun
                                                                                             (λ v₅ → CPSVal (CPSFun (λ t''' → k₁ (CPSVar v₅) (CPSVar t'''))))))
                                                                                           (CPSVal (CPSVar v₄)))
                                                                                          (CPSVal (CPSVar t''''))))))))
                                                                                (CPSVal t₄)))
                                                                {k₂ = (λ v₂ →
                                                                             cpsTerm e₂
                                                                             (λ v₃ t₄ →
                                                                                CPSApp
                                                                                (CPSApp (CPSApp (CPSVal v₂) (CPSVal v₃))
                                                                                 (CPSVal
                                                                                  (CPSFun
                                                                                   (λ v₄ →
                                                                                      CPSVal
                                                                                      (CPSFun
                                                                                       (λ t'''' →
                           (CPSApp
                            (CPSVal (CPSFun (λ t''' → k₁ (CPSVar v₄) (CPSVar t'''))))
                             (CPSVal (CPSVar t'''')))))))))
                                                                                (CPSVal t₄)))}
                                                                          (λ v t → kSubst e₂
                                                                                       (λ x₈ →
                                                                                          λ v₃ t₄ →
                                                                                            CPSApp
                                                                                            (CPSApp (CPSApp (CPSVal x₈) (CPSVal v₃))
                                                                                             (CPSVal
                                                                                              (CPSFun
                                                                                               (λ v₄ →
                                                                                                  CPSVal
                                                                                                  (CPSFun
                                                                                                   (λ t'''' →
                                                                                                      CPSApp
                                                                                                      (CPSApp
                                                                                                       (CPSVal
                                                                                                        (CPSFun
                                                                                                         (λ v₅ → CPSVal (CPSFun (λ t''' → k₁ (CPSVar v₅) (CPSVar t'''))))))
                                                                                                       (CPSVal (CPSVar v₄)))
                                                                                                      (CPSVal (CPSVar t''''))))))))
                                                                                            (CPSVal t₄))

 (λ x₈ t₄ → sApp (sApp (sApp (sVal sVar=) Subst≠) Subst≠) Subst≠))
 (λ v t → correctCont e₂
              (λ v₃ t₄ →
                 CPSApp
                 (CPSApp (CPSApp (CPSVal (cpsV v)) (CPSVal v₃))
                  (CPSVal
                   (CPSFun
                    (λ v₄ →
                       CPSVal
                       (CPSFun
                        (λ t'''' →
                           CPSApp
                           (CPSApp
                            (CPSVal
                             (CPSFun
                              (λ v₅ → CPSVal (CPSFun (λ t''' → k₁ (CPSVar v₅) (CPSVar t'''))))))
                            (CPSVal (CPSVar v₄)))
                           (CPSVal (CPSVar t''''))))))))
                 (CPSVal t₄))
                 {k₂ = (λ v₃ t₄ →
                 CPSApp
                 (CPSApp (CPSApp (CPSVal (cpsV v)) (CPSVal v₃))
                  (CPSVal
                   (CPSFun
                    (λ v₄ →
                       CPSVal
                       (CPSFun
                        (λ t'''' →
                           (CPSApp
                            (CPSVal (CPSFun (λ t''' → k₁ (CPSVar v₄) (CPSVar t'''))))
                             (CPSVal (CPSVar t'''')))))))))
                 (CPSVal t₄))}
              (λ v₂ t₄ → sApp (sApp (sApp Subst≠ (sVal sVar=)) Subst≠) Subst≠)
              (λ v₂ t₄ → rApp₁ (rApp₂ (rFun (λ x₈ → rFun (λ x₉ → rApp₁ (rBeta (sVal (sFun (λ x₁₀ → sch (CPSVar x₈) (CPSVar x₁₀)))))))))))))))) ⟩

  CPSLet
    (CPSVal
     (CPSFun
      (λ z →
         CPSVal
         (CPSFun
          (λ z₁ →
             CPSVal
             (CPSFun
              (λ z₂ →
                 CPSLet
                 (CPSVal (CPSAppend refl t₁
                  (CPSCons x₂ (CPSVar z₁)
                   (CPSVar z₂))))
                 (λ z₃ →
                    cpsTerm (pcontext-plug p₃' (Val (Var z)))
                    (λ v₂ →
                       cpsTerm e₂
                       (λ v₃ t₄ →
                          CPSApp
                          (CPSApp (CPSApp (CPSVal v₂) (CPSVal v₃))
                           (CPSVal
                            (CPSFun
                             (λ v₄ →
                                CPSVal
                                (CPSFun
                                 (λ t'''' →
                                    CPSApp
                                    (CPSApp
                                     (CPSVal
                                      (CPSFun
                                       (λ v₅ →
                                          CPSVal (CPSFun (λ t''' → k₁ (CPSVar v₅) (CPSVar t'''))))))
                                     (CPSVal (CPSVar v₄)))
                                    (CPSVal (CPSVar t''''))))))))
                          (CPSVal t₄)))
                    (CPSVar z₃)))))))))
    (λ x' → cpsTerm (e x') (CPSIdk x₁) CPSId)
  ⟵⟨ rLet₁ (rFun (λ x → rFun (λ x₅ → rFun (λ x₆ → rLet₂ (λ x₇ → rBeta (tSubst (pcontext-plug p₃' (Val (Var x)))
     (λ t v₂ → tSubst e₂ (λ t₄ v₃ → sApp Subst≠ (sVal sVar=))))))))) ⟩
  CPSLet
    (CPSVal
     (CPSFun
      (λ z →
         CPSVal
         (CPSFun
          (λ z₁ →
             CPSVal
             (CPSFun
              (λ z₂ →
                 CPSLet
                 (CPSVal (CPSAppend refl t₁
                  (CPSCons x₂ (CPSVar z₁)
                   (CPSVar z₂))))
                 (λ z₃ →
                    CPSApp
                    (CPSVal
                     (CPSFun
                      (λ z₄ →
                         cpsTerm (pcontext-plug p₃' (Val (Var z)))
                         (λ v₂ →
                            cpsTerm e₂
                            (λ v₃ t₄ →
                               CPSApp
                               (CPSApp (CPSApp (CPSVal v₂) (CPSVal v₃))
                                (CPSVal
                                 (CPSFun
                                  (λ v₄ →
                                     CPSVal
                                     (CPSFun
                                      (λ t'''' →
                                         CPSApp
                                         (CPSApp
                                          (CPSVal
                                           (CPSFun
                                            (λ v₅ →
                                               CPSVal
                                               (CPSFun (λ t''' → k₁ (CPSVar v₅) (CPSVar t'''))))))
                                          (CPSVal (CPSVar v₄)))
                                         (CPSVal (CPSVar t''''))))))))
                               (CPSVal t₄)))
                         (CPSVar z₄))))
                    (CPSVal (CPSVar z₃))))))))))
    (λ x' → cpsTerm (e x') (CPSIdk x₁) CPSId)
  ⟵⟨ rLet₁ (rFun (λ x → rFun (λ x₅ → rFun (λ x₆ → rLet₂ (λ x₇ → rApp₁ (rBeta
      (sVal (sFun (λ x₈ → kSubst (pcontext-plug p₃' (Val (Var x)))
                              (λ y →
                                 λ v₂ →
                                   cpsTerm e₂
                                   (λ v₃ t₄ →
                                      CPSApp
                                      (CPSApp (CPSApp (CPSVal v₂) (CPSVal v₃))
                                       (CPSVal
                                        (CPSFun
                                         (λ v₄ →
                                            CPSVal
                                            (CPSFun
                                             (λ t'''' →
                                                CPSApp (CPSApp (CPSVal y) (CPSVal (CPSVar v₄)))
                                                (CPSVal (CPSVar t''''))))))))
                                      (CPSVal t₄)))
                              (λ x₉ t → kSubst e₂
                                            (λ x₁₀ →
                                               λ v₃ t₄ →
                                                 CPSApp
                                                 (CPSApp (CPSApp (CPSVal x₉) (CPSVal v₃))
                                                  (CPSVal
                                                   (CPSFun
                                                    (λ v₄ →
                                                       CPSVal
                                                       (CPSFun
                                                        (λ t'''' →
                                                           CPSApp (CPSApp (CPSVal x₁₀) (CPSVal (CPSVar v₄)))
                                                           (CPSVal (CPSVar t''''))))))))
                                                 (CPSVal t₄))
                                            (λ x₁₀ t₄ → sApp (sApp Subst≠ (sVal (sFun (λ x₁₁ → sVal (sFun (λ x₁₂ → sApp (sApp (sVal sVar=) Subst≠) Subst≠)))))) Subst≠))))))))))) ⟩
  CPSLet
    (CPSVal
     (CPSFun
      (λ z →
         CPSVal
         (CPSFun
          (λ z₁ →
             CPSVal
             (CPSFun
              (λ z₂ →
                 CPSLet
                 (CPSVal (CPSAppend refl t₁
                  (CPSCons x₂ (CPSVar z₁)
                   (CPSVar z₂))))
                 (λ z₃ →
                    CPSApp
                    (CPSApp
                     (CPSVal
                      (CPSFun
                       (λ z₄ →
                          CPSVal
                          (CPSFun
                           (λ z₅ →
                              cpsTerm (pcontext-plug p₃' (Val (Var z)))
                              (λ v₂ →
                                 cpsTerm e₂
                                 (λ v₃ t₄ →
                                    CPSApp
                                    (CPSApp (CPSApp (CPSVal v₂) (CPSVal v₃))
                                     (CPSVal
                                      (CPSFun
                                       (λ v₄ →
                                          CPSVal
                                          (CPSFun
                                           (λ t'''' →
                                              CPSApp (CPSApp (CPSVal (CPSVar z₄)) (CPSVal (CPSVar v₄)))
                                              (CPSVal (CPSVar t''''))))))))
                                    (CPSVal t₄)))
                              (CPSVar z₅))))))
                     (CPSVal
                      (CPSFun
                       (λ v₂ → CPSVal (CPSFun (λ t''' → k₁ (CPSVar v₂) (CPSVar t''')))))))
                    (CPSVal (CPSVar z₃))))))))))
    (λ x' → cpsTerm (e x') (CPSIdk x₁) CPSId)
  ⟵⟨ rLet₁ (rFun (λ x → rFun (λ x₅ → rFun (λ x₆ → rLet₂ (λ x₇ → rApp₁ (rApp₁ (rBeta
      (sVal (sFun (λ x₈ → sVal (sFun (λ x₉ → eSubst (subst-context p₃' ((Var x)))
      (λ {v₂}  x₁₀ → kSubst′′ e₂
                         (λ x₁₁ →
                            λ v₃ t₄ →
                              CPSApp
                              (CPSApp (CPSApp (CPSVal (v₂ x₁₁)) (CPSVal v₃))
                               (CPSVal
                                (CPSFun
                                 (λ v₄ →
                                    CPSVal
                                    (CPSFun
                                     (λ t'''' →
                                        CPSApp (CPSApp (CPSVal (CPSVar x₈)) (CPSVal (CPSVar v₄)))
                                        (CPSVal (CPSVar t''''))))))))
                              (CPSVal t₄))
                         (λ x₁₁ → sApp (sApp (sApp (sVal x₁₀) (sVal x₁₁)) Subst≠) Subst≠)))))))))))))) ⟩
  (CPSLet
       (CPSVal
        (CPSFun
         (λ v →
            CPSVal
            (CPSFun
             (λ k' →
                CPSVal
                (CPSFun
                 (λ t' →
                    CPSLet
                    (CPSVal (CPSAppend refl t₁
                     (CPSCons x₂ (CPSVar k')
                      (CPSVar t'))))
                    (λ t'' →
                       CPSApp
                       (CPSApp
                        (CPSApp
                         (CPSVal
                          (CPSFun
                           (λ x →
                              CPSVal
                              (CPSFun
                               (λ k'' →
                                  CPSVal
                                  (CPSFun
                                   (λ t''' →
                                      cpsTerm (pcontext-plug p₃' (Val (Var x)))
                                      (λ v₂ →
                                         cpsTerm e₂
                                         (λ v₃ t₄ →
                                            CPSApp
                                            (CPSApp (CPSApp (CPSVal v₂) (CPSVal v₃))
                                             (CPSVal
                                              (CPSFun
                                               (λ v₄ →
                                                  CPSVal
                                                  (CPSFun
                                                   (λ t'''' →
                                                      CPSApp
                                                      (CPSApp (CPSVal (CPSVar k''))
                                                       (CPSVal (CPSVar v₄)))
                                                      (CPSVal (CPSVar t''''))))))))
                                            (CPSVal t₄)))
                                      (CPSVar t'''))))))))
                         (CPSVal (CPSVar v)))
                        (CPSVal
                         (CPSFun
                          (λ v₂ → CPSVal (CPSFun (λ t''' → k₁ (CPSVar v₂) (CPSVar t''')))))))
                       (CPSVal (CPSVar t''))))))))))
       (λ x' → cpsTerm (e x') (CPSIdk x₁) CPSId))
  ∎-}
-- control-lemma  (Frame (App₁ e₂) p₁') (Frame (App₁ .e₂) p₃') x₁ x₂ x₃
--               (Frame {f₁ = (App₁ e₂)}{f₂ = (App₁ .e₂)} (App₁ .e₂) {c₁ = c₁}{c₂ = c₂} x₄) e k₁ t₁ k₂ sch sch' = begin
--control-lemma p₁' p₃' x₁ x₂ x₃ x₄ e
control-lemma (Frame (App₂ v₁) p₁') (Frame (App₂ .v₁) p₃') x₁ x₂ x₃
              (Frame {f₁ = (App₂ v₁)}{f₂ = (App₂ .v₁)} (App₂ .v₁) {c₁ = c₁}{c₂ = c₂} x₄) e k₁ t₁ sch sch' = {!!}

{-begin
   (cpsTerm (pcontext-plug p₁' (Control x₁ x₂ x₃ e))
       (λ v₂ t₄ →
          CPSApp
          (CPSApp (CPSApp (CPSVal (cpsV v₁)) (CPSVal v₂))
           (CPSVal
            (CPSFun
             (λ v → CPSVal (CPSFun (λ t'' → k₁ (CPSVar v) (CPSVar t'')))))))
          (CPSVal t₄))
       t₁)
  ⟶⟨ control-lemma p₁' p₃' x₁ x₂ x₃ x₄ e
       (λ v₂ t₄ →
          CPSApp
          (CPSApp (CPSApp (CPSVal (cpsV v₁)) (CPSVal v₂))
           (CPSVal
            (CPSFun
             (λ v → CPSVal (CPSFun (λ t'' → k₁ (CPSVar v) (CPSVar t'')))))))
          (CPSVal t₄))
       t₁ (λ v t → sApp (sApp (sApp Subst≠ (sVal sVar=)) Subst≠) Subst≠)
       (λ t v₂ → sApp Subst≠ (sVal sVar=)) ⟩
  cpsTerm
    (App (Val (Fun (λ x → pcontext-plug p₃' (Val (Var x)))))
     (Control x₁ x₂ refl e))
    (λ v₂ t₄ →
       CPSApp
       (CPSApp (CPSApp (CPSVal (cpsV v₁)) (CPSVal v₂))
        (CPSVal
         (CPSFun
          (λ v → CPSVal (CPSFun (λ t'' → k₁ (CPSVar v) (CPSVar t'')))))))
       (CPSVal t₄))
    t₁
  ≡⟨ refl ⟩
  (CPSLet
       (CPSVal
        (CPSFun
         (λ v →
            CPSVal
            (CPSFun
             (λ k' →
                CPSVal
                (CPSFun
                 (λ t' →
                    CPSLet
                    (CPSVal (CPSAppend refl t₁
                     (CPSCons x₂ (CPSVar k')
                      (CPSVar t'))))
                    (λ t'' →
                       CPSApp
                       (CPSApp
                        (CPSApp
                         (CPSVal
                          (CPSFun
                           (λ x →
                              CPSVal
                              (CPSFun
                               (λ k'' →
                                  CPSVal
                                  (CPSFun
                                   (λ t''' →
                                      cpsTerm (pcontext-plug p₃' (Val (Var x)))
                                      (λ v₂ t'''' →
                                         CPSApp (CPSApp (CPSVal (CPSVar k'')) (CPSVal v₂))
                                         (CPSVal t''''))
                                      (CPSVar t'''))))))))
                         (CPSVal (CPSVar v)))
                        (CPSVal
                         (CPSFun
                          (λ v₂ →
                             CPSVal
                             (CPSFun
                              (λ t''' →
                                 CPSApp
                                 (CPSApp (CPSApp (CPSVal (cpsV v₁)) (CPSVal (CPSVar v₂)))
                                  (CPSVal
                                   (CPSFun
                                    (λ v₃ →
                                       CPSVal (CPSFun (λ t'''' → k₁ (CPSVar v₃) (CPSVar t'''')))))))
                                 (CPSVal (CPSVar t'''))))))))
                       (CPSVal (CPSVar t''))))))))))
       (λ x' → cpsTerm (e x') (CPSIdk x₁) CPSId))
  ⟶⟨ rLet₁ (rFun (λ x → rFun (λ x₅ → rFun (λ x₆ → rLet₂ (λ x₇ → rApp₁ (rApp₁ (rBeta
      (sVal (sFun (λ x₈ → sVal (sFun (λ x₉ → eSubst (subst-context p₃' (Var x))
      (λ x₁₀ → sApp (sApp Subst≠ (sVal x₁₀)) Subst≠))))))))))))) ⟩
  CPSLet
    (CPSVal
     (CPSFun
      (λ z →
         CPSVal
         (CPSFun
          (λ z₁ →
             CPSVal
             (CPSFun
              (λ z₂ →
                 CPSLet
                 (CPSVal (CPSAppend refl t₁
                  (CPSCons x₂ (CPSVar z₁)
                   (CPSVar z₂))))
                 (λ z₃ →
                    CPSApp
                    (CPSApp
                     (CPSVal
                      (CPSFun
                       (λ z₄ →
                          CPSVal
                          (CPSFun
                           (λ z₅ →
                              cpsTerm (pcontext-plug p₃' (Val (Var z)))
                              (λ v₂ t'''' →
                                 CPSApp (CPSApp (CPSVal (CPSVar z₄)) (CPSVal v₂)) (CPSVal t''''))
                              (CPSVar z₅))))))
                     (CPSVal
                      (CPSFun
                       (λ v₂ →
                          CPSVal
                          (CPSFun
                           (λ t''' →
                              CPSApp
                              (CPSApp (CPSApp (CPSVal (cpsV v₁)) (CPSVal (CPSVar v₂)))
                               (CPSVal
                                (CPSFun
                                 (λ v₃ →
                                    CPSVal (CPSFun (λ t'''' → k₁ (CPSVar v₃) (CPSVar t'''')))))))
                              (CPSVal (CPSVar t'''))))))))
                    (CPSVal (CPSVar z₃))))))))))
    (λ x' → cpsTerm (e x') (CPSIdk x₁) CPSId)
  ⟶⟨ rLet₁ (rFun (λ x → rFun (λ x₅ → rFun (λ x₆ → rLet₂ (λ x₇ → rApp₁ (rBeta
      (sVal (sFun (λ x₈ → kSubst (pcontext-plug p₃' (Val (Var x))) ((λ y → (λ v₂ t'''' →
            CPSApp (CPSApp (CPSVal y) (CPSVal v₂)) (CPSVal t''''))))
            (λ x₉ t → sApp (sApp (sVal sVar=) Subst≠) Subst≠)))))))))) ⟩
  CPSLet
    (CPSVal
     (CPSFun
      (λ z →
         CPSVal
         (CPSFun
          (λ z₁ →
             CPSVal
             (CPSFun
              (λ z₂ →
                 CPSLet
                 (CPSVal (CPSAppend refl t₁
                  (CPSCons x₂ (CPSVar z₁)
                   (CPSVar z₂))))
                 (λ z₃ →
                    CPSApp
                    (CPSVal
                     (CPSFun
                      (λ z₄ →
                         cpsTerm (pcontext-plug p₃' (Val (Var z)))
                         (λ v₂ t'''' →
                            CPSApp
                            (CPSApp
                             (CPSVal
                              (CPSFun
                               (λ v₃ →
                                  CPSVal
                                  (CPSFun
                                   (λ t''' →
                                      CPSApp
                                      (CPSApp (CPSApp (CPSVal (cpsV v₁)) (CPSVal (CPSVar v₃)))
                                       (CPSVal
                                        (CPSFun
                                         (λ v₄ →
                                            CPSVal
                                            (CPSFun (λ t''''' → k₁ (CPSVar v₄) (CPSVar t''''')))))))
                                      (CPSVal (CPSVar t''')))))))
                             (CPSVal v₂))
                            (CPSVal t''''))
                         (CPSVar z₄))))
                    (CPSVal (CPSVar z₃))))))))))
    (λ x' → cpsTerm (e x') (CPSIdk x₁) CPSId)
  ⟶⟨ rLet₁ (rFun (λ x → rFun (λ x₅ → rFun (λ x₆ → rLet₂ (λ x₇ → rBeta
      (tSubst (pcontext-plug p₃' (Val (Var x))) (λ t v₂ → sApp Subst≠ (sVal sVar=)))))))) ⟩
  CPSLet
    (CPSVal
     (CPSFun
      (λ z →
         CPSVal
         (CPSFun
          (λ z₁ →
             CPSVal
             (CPSFun
              (λ z₂ →
                 CPSLet
                 (CPSVal (CPSAppend refl t₁
                  (CPSCons x₂ (CPSVar z₁)
                   (CPSVar z₂))))
                 (λ z₃ →
                    cpsTerm (pcontext-plug p₃' (Val (Var z)))
                    (λ v₂ t'''' →
                       CPSApp
                       (CPSApp
                        (CPSVal
                         (CPSFun
                          (λ v₃ →
                             CPSVal
                             (CPSFun
                              (λ t''' →
                                 CPSApp
                                 (CPSApp (CPSApp (CPSVal (cpsV v₁)) (CPSVal (CPSVar v₃)))
                                  (CPSVal
                                   (CPSFun
                                    (λ v₄ →
                                       CPSVal (CPSFun (λ t''''' → k₁ (CPSVar v₄) (CPSVar t''''')))))))
                                 (CPSVal (CPSVar t''')))))))
                        (CPSVal v₂))
                       (CPSVal t''''))
                    (CPSVar z₃)))))))))
    (λ x' → cpsTerm (e x') (CPSIdk x₁) CPSId)
  ⟶⟨ rLet₁ (rFun (λ x → rFun (λ x₅ → rFun (λ x₆ → rLet₂ (λ x₇ →
     correctCont (pcontext-plug p₃' (Val (Var x)))
       (λ v₂ t'''' →
          CPSApp
          (CPSApp
           (CPSVal
            (CPSFun
             (λ v₃ →
                CPSVal
                (CPSFun
                 (λ t''' →
                    CPSApp
                    (CPSApp (CPSApp (CPSVal (cpsV v₁)) (CPSVal (CPSVar v₃)))
                     (CPSVal
                      (CPSFun
                       (λ v₄ →
                          CPSVal (CPSFun (λ t''''' → k₁ (CPSVar v₄) (CPSVar t''''')))))))
                    (CPSVal (CPSVar t''')))))))
           (CPSVal v₂))
          (CPSVal t''''))
          {k₂ = (λ v₂ t'''' →
          CPSApp
           
                (CPSVal
                (CPSFun
                 (λ t''' →
                    CPSApp
                    (CPSApp (CPSApp (CPSVal (cpsV v₁)) (CPSVal v₂))
                     (CPSVal
                      (CPSFun
                       (λ v₄ →
                          CPSVal (CPSFun (λ t''''' → k₁ (CPSVar v₄) (CPSVar t''''')))))))
                    (CPSVal (CPSVar t'''))))
           )
          (CPSVal t''''))}
       (λ v t → sApp (sApp Subst≠ (sVal sVar=)) Subst≠) λ v t → rApp₁ (rBeta
       (sVal (sFun (λ x₈ → sApp (sApp (sApp Subst≠ (sVal sVar=)) Subst≠) Subst≠)))) ))))) ⟩
  CPSLet
    (CPSVal
     (CPSFun
      (λ z →
         CPSVal
         (CPSFun
          (λ z₁ →
             CPSVal
             (CPSFun
              (λ z₂ →
                 CPSLet
                 (CPSVal (CPSAppend refl t₁
                  (CPSCons x₂ (CPSVar z₁)
                   (CPSVar z₂))))
                 (λ z₃ →
                    cpsTerm (pcontext-plug p₃' (Val (Var z)))
                    (λ v₂ t'''' →
                       CPSApp
                       (CPSVal
                        (CPSFun
                         (λ t''' →
                            CPSApp
                            (CPSApp (CPSApp (CPSVal (cpsV v₁)) (CPSVal v₂))
                             (CPSVal
                              (CPSFun
                               (λ v₄ →
                                  CPSVal (CPSFun (λ t''''' → k₁ (CPSVar v₄) (CPSVar t''''')))))))
                            (CPSVal (CPSVar t''')))))
                       (CPSVal t''''))
                    (CPSVar z₃)))))))))
    (λ x' → cpsTerm (e x') (CPSIdk x₁) CPSId)
  ⟶⟨ rLet₁ (rFun (λ x → rFun (λ x₅ → rFun (λ x₆ → rLet₂ (λ x₇ →
      correctCont (pcontext-plug p₃' (Val (Var x)))
        (λ v₂ t'''' →
           CPSApp
           (CPSVal
            (CPSFun
             (λ t''' →
                CPSApp
                (CPSApp (CPSApp (CPSVal (cpsV v₁)) (CPSVal v₂))
                 (CPSVal
                  (CPSFun
                   (λ v₄ →
                      CPSVal (CPSFun (λ t''''' → k₁ (CPSVar v₄) (CPSVar t''''')))))))
                (CPSVal (CPSVar t''')))))
           (CPSVal t''''))
           {k₂ = (λ v₂ t'''' →
           CPSApp
               (CPSApp (CPSApp (CPSVal (cpsV v₁)) (CPSVal v₂))
                (CPSVal
                 (CPSFun
                  (λ v₄ →
                     CPSVal (CPSFun (λ t''''' → k₁ (CPSVar v₄) (CPSVar t''''')))))))
               (CPSVal t''''))}
        (λ v t → sApp (sVal (sFun (λ x₈ → sApp (sApp (sApp Subst≠ (sVal sVar=)) Subst≠) Subst≠))) Subst≠)
        λ v t → rBeta (sApp Subst≠ (sVal sVar=))))))) ⟩
  CPSLet
    (CPSVal
     (CPSFun
      (λ z →
         CPSVal
         (CPSFun
          (λ z₁ →
             CPSVal
             (CPSFun
              (λ z₂ →
                 CPSLet
                 (CPSVal (CPSAppend refl t₁
                  (CPSCons x₂ (CPSVar z₁)
                   (CPSVar z₂))))
                 (λ z₃ →
                    cpsTerm (pcontext-plug p₃' (Val (Var z)))
                    (λ v₂ t'''' →
                       CPSApp
                       (CPSApp (CPSApp (CPSVal (cpsV v₁)) (CPSVal v₂))
                        (CPSVal
                         (CPSFun
                          (λ v₄ →
                             CPSVal (CPSFun (λ t''''' → k₁ (CPSVar v₄) (CPSVar t''''')))))))
                       (CPSVal t''''))
                    (CPSVar z₃)))))))))
    (λ x' → cpsTerm (e x') (CPSIdk x₁) CPSId)
  ⟵⟨ rLet₁ (rFun (λ x → rFun (λ x₅ → rFun (λ x₆ → rLet₂ (λ x₇ →
      correctCont (pcontext-plug p₃' (Val (Var x)))
        (λ v₂ t₄ →
           CPSApp
           (CPSApp (CPSApp (CPSVal (cpsV v₁)) (CPSVal v₂))
            (CPSVal
             (CPSFun
              (λ v₃ →
                 CPSVal
                 (CPSFun
                  (λ t'''' →
                     CPSApp (CPSVal (CPSFun (λ t''' → k₁ (CPSVar v₃) (CPSVar t'''))))
                     (CPSVal (CPSVar t''''))))))))
           (CPSVal t₄))
           {k₂ = (λ v₂ t₄ →
          CPSApp
          (CPSApp (CPSApp (CPSVal (cpsV v₁)) (CPSVal v₂))
           (CPSVal
            (CPSFun
             (λ v₃ →
                CPSVal
                (CPSFun
                 (λ t'''' →  k₁ (CPSVar v₃) (CPSVar t'''')))))))
          (CPSVal t₄))}
        (λ v t → sApp (sApp (sApp Subst≠ (sVal sVar=)) Subst≠) Subst≠) λ v t →
        rApp₁ (rApp₂ (rFun (λ x₈ → rFun (λ x₉ → rBeta (sch' (CPSVar x₉) (CPSVar x₈))))))))))) ⟩
  CPSLet
    (CPSVal
     (CPSFun
      (λ z →
         CPSVal
         (CPSFun
          (λ z₁ →
             CPSVal
             (CPSFun
              (λ z₂ →
                 CPSLet
                 (CPSVal (CPSAppend refl t₁
                  (CPSCons x₂ (CPSVar z₁)
                   (CPSVar z₂))))
                 (λ z₃ →
                    cpsTerm (pcontext-plug p₃' (Val (Var z)))
                    (λ v₂ t₄ →
                       CPSApp
                       (CPSApp (CPSApp (CPSVal (cpsV v₁)) (CPSVal v₂))
                        (CPSVal
                         (CPSFun
                          (λ v₃ →
                             CPSVal
                             (CPSFun
                              (λ t'''' →
                                 CPSApp (CPSVal (CPSFun (λ t''' → k₁ (CPSVar v₃) (CPSVar t'''))))
                                 (CPSVal (CPSVar t''''))))))))
                       (CPSVal t₄))
                    (CPSVar z₃)))))))))
    (λ x' → cpsTerm (e x') (CPSIdk x₁) CPSId)
  ⟵⟨ rLet₁ (rFun (λ x → rFun (λ x₅ → rFun (λ x₆ → rLet₂ (λ x₇ →
      correctCont (pcontext-plug p₃' (Val (Var x)))
        (λ v₂ t₄ →
           CPSApp
           (CPSApp (CPSApp (CPSVal (cpsV v₁)) (CPSVal v₂))
            (CPSVal
             (CPSFun
              (λ v₃ →
                 CPSVal
                 (CPSFun
                  (λ t'''' →
                     CPSApp
                     (CPSApp
                      (CPSVal
                       (CPSFun
                        (λ v₄ → CPSVal (CPSFun (λ t''' → k₁ (CPSVar v₄) (CPSVar t'''))))))
                      (CPSVal (CPSVar v₃)))
                     (CPSVal (CPSVar t''''))))))))
           (CPSVal t₄))
           {k₂ = (λ v₂ t₄ →
          CPSApp
          (CPSApp (CPSApp (CPSVal (cpsV v₁)) (CPSVal v₂))
           (CPSVal
            (CPSFun
             (λ v₃ →
                CPSVal
                (CPSFun
                 (λ t'''' →
                    CPSApp
                      (CPSVal (CPSFun (λ t''' → k₁ (CPSVar v₃) (CPSVar t'''))))
                     (CPSVal (CPSVar t''''))
                    ))))))
          (CPSVal t₄))}
        (λ v t → sApp (sApp (sApp Subst≠ (sVal sVar=)) Subst≠) Subst≠) λ v t →
        rApp₁ (rApp₂ (rFun (λ x₈ → rFun (λ x₉ → rApp₁ (rBeta (sVal (sFun (λ x₁₀ → sch (CPSVar x₈) (CPSVar x₁₀)))))))))))))) ⟩
  CPSLet
    (CPSVal
     (CPSFun
      (λ z →
         CPSVal
         (CPSFun
          (λ z₁ →
             CPSVal
             (CPSFun
              (λ z₂ →
                 CPSLet
                 (CPSVal (CPSAppend refl t₁
                  (CPSCons x₂ (CPSVar z₁)
                   (CPSVar z₂))))
                 (λ z₃ →
                    cpsTerm (pcontext-plug p₃' (Val (Var z)))
                    (λ v₂ t₄ →
                       CPSApp
                       (CPSApp (CPSApp (CPSVal (cpsV v₁)) (CPSVal v₂))
                        (CPSVal
                         (CPSFun
                          (λ v₃ →
                             CPSVal
                             (CPSFun
                              (λ t'''' →
                                 CPSApp
                                 (CPSApp
                                  (CPSVal
                                   (CPSFun
                                    (λ v₄ → CPSVal (CPSFun (λ t''' → k₁ (CPSVar v₄) (CPSVar t'''))))))
                                  (CPSVal (CPSVar v₃)))
                                 (CPSVal (CPSVar t''''))))))))
                       (CPSVal t₄))
                    (CPSVar z₃)))))))))
    (λ x' → cpsTerm (e x') (CPSIdk x₁) CPSId)
  ⟵⟨ rLet₁ (rFun (λ x → rFun (λ x₅ → rFun (λ x₆ → rLet₂ (λ x₇ → rBeta
      (tSubst (pcontext-plug p₃' (Val (Var x)))
      (λ t v₂ → sApp Subst≠ (sVal sVar=)))))))) ⟩
  CPSLet
    (CPSVal
     (CPSFun
      (λ z →
         CPSVal
         (CPSFun
          (λ z₁ →
             CPSVal
             (CPSFun
              (λ z₂ →
                 CPSLet
                 (CPSVal (CPSAppend refl t₁
                  (CPSCons x₂ (CPSVar z₁)
                   (CPSVar z₂))))
                 (λ z₃ →
                    CPSApp
                    (CPSVal
                     (CPSFun
                      (λ z₄ →
                         cpsTerm (pcontext-plug p₃' (Val (Var z)))
                         (λ v₂ t₄ →
                            CPSApp
                            (CPSApp (CPSApp (CPSVal (cpsV v₁)) (CPSVal v₂))
                             (CPSVal
                              (CPSFun
                               (λ v₃ →
                                  CPSVal
                                  (CPSFun
                                   (λ t'''' →
                                      CPSApp
                                      (CPSApp
                                       (CPSVal
                                        (CPSFun
                                         (λ v₄ →
                                            CPSVal (CPSFun (λ t''' → k₁ (CPSVar v₄) (CPSVar t'''))))))
                                       (CPSVal (CPSVar v₃)))
                                      (CPSVal (CPSVar t''''))))))))
                            (CPSVal t₄))
                         (CPSVar z₄))))
                    (CPSVal (CPSVar z₃))))))))))
    (λ x' → cpsTerm (e x') (CPSIdk x₁) CPSId)
  ⟵⟨ rLet₁ (rFun (λ x → rFun (λ x₅ → rFun (λ x₆ → rLet₂ (λ x₇ →
      rApp₁ (rBeta (sVal (sFun (λ x₈ →
      kSubst (pcontext-plug p₃' (Val (Var x)))
        (λ y →
           λ v₂ t₄ →
             CPSApp
             (CPSApp (CPSApp (CPSVal (cpsV v₁)) (CPSVal v₂))
              (CPSVal
               (CPSFun
                (λ v₃ →
                   CPSVal
                   (CPSFun
                    (λ t'''' →
                       CPSApp (CPSApp (CPSVal y) (CPSVal (CPSVar v₃)))
                       (CPSVal (CPSVar t''''))))))))
             (CPSVal t₄))
        (λ x₉ t → sApp (sApp Subst≠ (sVal (sFun (λ x₁₀ → sVal (sFun (λ x₁₁ →
        sApp (sApp (sVal sVar=) Subst≠) Subst≠)))))) Subst≠)))))))))) ⟩
  CPSLet
    (CPSVal
     (CPSFun
      (λ z →
         CPSVal
         (CPSFun
          (λ z₁ →
             CPSVal
             (CPSFun
              (λ z₂ →
                 CPSLet
                 (CPSVal (CPSAppend refl t₁
                  (CPSCons x₂ (CPSVar z₁)
                   (CPSVar z₂))))
                 (λ z₃ →
                    CPSApp
                    (CPSApp
                     (CPSVal
                      (CPSFun
                       (λ z₄ →
                          CPSVal
                          (CPSFun
                           (λ z₅ →
                              cpsTerm (pcontext-plug p₃' (Val (Var z)))
                              (λ v₂ t₄ →
                                 CPSApp
                                 (CPSApp (CPSApp (CPSVal (cpsV v₁)) (CPSVal v₂))
                                  (CPSVal
                                   (CPSFun
                                    (λ v₃ →
                                       CPSVal
                                       (CPSFun
                                        (λ t'''' →
                                           CPSApp (CPSApp (CPSVal (CPSVar z₄)) (CPSVal (CPSVar v₃)))
                                           (CPSVal (CPSVar t''''))))))))
                                 (CPSVal t₄))
                              (CPSVar z₅))))))
                     (CPSVal
                      (CPSFun
                       (λ v₂ → CPSVal (CPSFun (λ t''' → k₁ (CPSVar v₂) (CPSVar t''')))))))
                    (CPSVal (CPSVar z₃))))))))))
    (λ x' → cpsTerm (e x') (CPSIdk x₁) CPSId)
  ⟵⟨ rLet₁ (rFun (λ x → rFun (λ x₅ → rFun (λ x₆ → rLet₂ (λ x₇ →
      rApp₁ (rApp₁ (rBeta (sVal (sFun (λ x₈ → sVal (sFun (λ x₉ → eSubst (subst-context p₃' (Var x))
      (λ x₁₀ → sApp (sApp (sApp Subst≠ (sVal x₁₀)) Subst≠) Subst≠))))))))))))) ⟩
  (CPSLet
       (CPSVal
        (CPSFun
         (λ v →
            CPSVal
            (CPSFun
             (λ k' →
                CPSVal
                (CPSFun
                 (λ t' →
                    CPSLet
                    (CPSVal (CPSAppend refl t₁
                     (CPSCons x₂ (CPSVar k')
                      (CPSVar t'))))
                    (λ t'' →
                       CPSApp
                       (CPSApp
                        (CPSApp
                         (CPSVal
                          (CPSFun
                           (λ x →
                              CPSVal
                              (CPSFun
                               (λ k'' →
                                  CPSVal
                                  (CPSFun
                                   (λ t''' →
                                      cpsTerm (pcontext-plug p₃' (Val (Var x)))
                                      (λ v₂ t₄ →
                                         CPSApp
                                         (CPSApp (CPSApp (CPSVal (cpsV v₁)) (CPSVal v₂))
                                          (CPSVal
                                           (CPSFun
                                            (λ v₃ →
                                               CPSVal
                                               (CPSFun
                                                (λ t'''' →
                                                   CPSApp
                                                   (CPSApp (CPSVal (CPSVar k''))
                                                    (CPSVal (CPSVar v₃)))
                                                   (CPSVal (CPSVar t''''))))))))
                                         (CPSVal t₄))
                                      (CPSVar t'''))))))))
                         (CPSVal (CPSVar v)))
                        (CPSVal
                         (CPSFun
                          (λ v₂ → CPSVal (CPSFun (λ t''' → k₁ (CPSVar v₂) (CPSVar t''')))))))
                       (CPSVal (CPSVar t''))))))))))
       (λ x' → cpsTerm (e x') (CPSIdk x₁) CPSId))
  ∎ -}


control-lemma (Frame (Plus₁ e₂) p₁') (Frame (Plus₁ .e₂) p₃') x₁ x₂ x₃
              (Frame {f₁ = (Plus₁ e₂)}{f₂ = (Plus₁ .e₂)} (Plus₁ .e₂) {c₁ = c₁}{c₂ = c₂} x₄) e k₁ t₁ sch sch' = {!!}

{- begin
  (cpsTerm (pcontext-plug p₁' (Control x₁ x₂ x₃ e))
       (λ v₁ →
          cpsTerm e₂
          (λ v₂ t₄ →
             CPSLet (CPSPlus (CPSVal v₁) (CPSVal v₂)) (λ v → k₁ (CPSVar v) t₄)))
       t₁)
  ⟶⟨ control-lemma p₁' p₃' x₁ x₂ x₃ x₄ e
       (λ v₁ →
          cpsTerm e₂
          (λ v₂ t₄ →
             CPSLet (CPSPlus (CPSVal v₁) (CPSVal v₂)) (λ v → k₁ (CPSVar v) t₄)))
       t₁ (λ v t →
       kSubst e₂
         (λ x →
            λ v₂ t₄ →
              CPSLet (CPSPlus (CPSVal x) (CPSVal v₂)) (λ v₁ → k₁ (CPSVar v₁) t₄))
         (λ x t₄ → sLet (λ x₅ → Subst≠) (λ x₅ → sPlu (sVal sVar=) Subst≠)))
         (λ t v₂ → tSubst e₂ (λ t₄ v₃ → sLet (λ x → sch' t₄ (CPSVar x)) (λ x → Subst≠))) ⟩
  cpsTerm
    (App (Val (Fun (λ x → pcontext-plug p₃' (Val (Var x)))))
     (Control x₁ x₂ refl e))
    (λ v₁ →
       cpsTerm e₂
       (λ v₂ t₄ →
          CPSLet (CPSPlus (CPSVal v₁) (CPSVal v₂)) (λ v → k₁ (CPSVar v) t₄)))
    t₁
  ≡⟨ refl ⟩
  (CPSLet
       (CPSVal
        (CPSFun
         (λ v →
            CPSVal
            (CPSFun
             (λ k' →
                CPSVal
                (CPSFun
                 (λ t' →
                    CPSLet
                    (CPSVal (CPSAppend refl t₁
                     (CPSCons x₂ (CPSVar k')
                      (CPSVar t'))))
                    (λ t'' →
                       CPSApp
                       (CPSApp
                        (CPSApp
                         (CPSVal
                          (CPSFun
                           (λ x →
                              CPSVal
                              (CPSFun
                               (λ k'' →
                                  CPSVal
                                  (CPSFun
                                   (λ t''' →
                                      cpsTerm (pcontext-plug p₃' (Val (Var x)))
                                      (λ v₁ t'''' →
                                         CPSApp (CPSApp (CPSVal (CPSVar k'')) (CPSVal v₁))
                                         (CPSVal t''''))
                                      (CPSVar t'''))))))))
                         (CPSVal (CPSVar v)))
                        (CPSVal
                         (CPSFun
                          (λ v₁ →
                             CPSVal
                             (CPSFun
                              (λ t''' →
                                 cpsTerm e₂
                                 (λ v₂ t₄ →
                                    CPSLet (CPSPlus (CPSVal (CPSVar v₁)) (CPSVal v₂))
                                    (λ v₃ → k₁ (CPSVar v₃) t₄))
                                 (CPSVar t''')))))))
                       (CPSVal (CPSVar t''))))))))))
       (λ x' → cpsTerm (e x') (CPSIdk x₁) CPSId))
  ⟶⟨ rLet₁ (rFun (λ x → rFun (λ x₅ → rFun (λ x₆ → rLet₂ (λ x₇ →
      rApp₁ (rApp₁ (rBeta (sVal (sFun (λ x₈ → sVal (sFun (λ x₉ → eSubst (subst-context p₃' (Var x))
      (λ x₁₀ → sApp (sApp Subst≠ (sVal x₁₀)) Subst≠))))))))))))) ⟩
  CPSLet
    (CPSVal
     (CPSFun
      (λ z →
         CPSVal
         (CPSFun
          (λ z₁ →
             CPSVal
             (CPSFun
              (λ z₂ →
                 CPSLet
                 (CPSVal (CPSAppend refl t₁
                  (CPSCons x₂ (CPSVar z₁)
                   (CPSVar z₂))))
                 (λ z₃ →
                    CPSApp
                    (CPSApp
                     (CPSVal
                      (CPSFun
                       (λ z₄ →
                          CPSVal
                          (CPSFun
                           (λ z₅ →
                              cpsTerm (pcontext-plug p₃' (Val (Var z)))
                              (λ v₁ t'''' →
                                 CPSApp (CPSApp (CPSVal (CPSVar z₄)) (CPSVal v₁)) (CPSVal t''''))
                              (CPSVar z₅))))))
                     (CPSVal
                      (CPSFun
                       (λ v₁ →
                          CPSVal
                          (CPSFun
                           (λ t''' →
                              cpsTerm e₂
                              (λ v₂ t₄ →
                                 CPSLet (CPSPlus (CPSVal (CPSVar v₁)) (CPSVal v₂))
                                 (λ v₃ → k₁ (CPSVar v₃) t₄))
                              (CPSVar t''')))))))
                    (CPSVal (CPSVar z₃))))))))))
    (λ x' → cpsTerm (e x') (CPSIdk x₁) CPSId)
  ⟶⟨ rLet₁ (rFun (λ x → rFun (λ x₅ → rFun (λ x₆ → rLet₂ (λ x₇ →
      rApp₁ (rBeta (sVal (sFun (λ x₈ →
      kSubst (pcontext-plug p₃' (Val (Var x)))
        (λ y →
           λ v₁ t'''' → CPSApp (CPSApp (CPSVal y) (CPSVal v₁)) (CPSVal t''''))
        (λ x₉ t → sApp (sApp (sVal sVar=) Subst≠) Subst≠)))))))))) ⟩
  CPSLet
    (CPSVal
     (CPSFun
      (λ z →
         CPSVal
         (CPSFun
          (λ z₁ →
             CPSVal
             (CPSFun
              (λ z₂ →
                 CPSLet
                 (CPSVal (CPSAppend refl t₁
                  (CPSCons x₂ (CPSVar z₁)
                   (CPSVar z₂))))
                 (λ z₃ →
                    CPSApp
                    (CPSVal
                     (CPSFun
                      (λ z₄ →
                         cpsTerm (pcontext-plug p₃' (Val (Var z)))
                         (λ v₁ t'''' →
                            CPSApp
                            (CPSApp
                             (CPSVal
                              (CPSFun
                               (λ v₂ →
                                  CPSVal
                                  (CPSFun
                                   (λ t''' →
                                      cpsTerm e₂
                                      (λ v₃ t₄ →
                                         CPSLet (CPSPlus (CPSVal (CPSVar v₂)) (CPSVal v₃))
                                         (λ v₄ → k₁ (CPSVar v₄) t₄))
                                      (CPSVar t'''))))))
                             (CPSVal v₁))
                            (CPSVal t''''))
                         (CPSVar z₄))))
                    (CPSVal (CPSVar z₃))))))))))
    (λ x' → cpsTerm (e x') (CPSIdk x₁) CPSId)
  ⟶⟨ rLet₁ (rFun (λ x → rFun (λ x₅ → rFun (λ x₆ → rLet₂ (λ x₇ → rBeta
      (tSubst (pcontext-plug p₃' (Val (Var x)))
      (λ t v₂ → sApp Subst≠ (sVal sVar=)))))))) ⟩
  CPSLet
    (CPSVal
     (CPSFun
      (λ z →
         CPSVal
         (CPSFun
          (λ z₁ →
             CPSVal
             (CPSFun
              (λ z₂ →
                 CPSLet
                 (CPSVal (CPSAppend refl t₁
                  (CPSCons x₂ (CPSVar z₁)
                   (CPSVar z₂))))
                 (λ z₃ →
                    cpsTerm (pcontext-plug p₃' (Val (Var z)))
                    (λ v₁ t'''' →
                       CPSApp
                       (CPSApp
                        (CPSVal
                         (CPSFun
                          (λ v₂ →
                             CPSVal
                             (CPSFun
                              (λ t''' →
                                 cpsTerm e₂
                                 (λ v₃ t₄ →
                                    CPSLet (CPSPlus (CPSVal (CPSVar v₂)) (CPSVal v₃))
                                    (λ v₄ → k₁ (CPSVar v₄) t₄))
                                 (CPSVar t'''))))))
                        (CPSVal v₁))
                       (CPSVal t''''))
                    (CPSVar z₃)))))))))
    (λ x' → cpsTerm (e x') (CPSIdk x₁) CPSId)
  ⟶⟨ rLet₁ (rFun (λ x → rFun (λ x₅ → rFun (λ x₆ → rLet₂ (λ x₇ →
      correctCont (pcontext-plug p₃' (Val (Var x)))
        (λ v₁ t'''' →
           CPSApp
           (CPSApp
            (CPSVal
             (CPSFun
              (λ v₂ →
                 CPSVal
                 (CPSFun
                  (λ t''' →
                     cpsTerm e₂
                     (λ v₃ t₄ →
                        CPSLet (CPSPlus (CPSVal (CPSVar v₂)) (CPSVal v₃))
                        (λ v₄ → k₁ (CPSVar v₄) t₄))
                     (CPSVar t'''))))))
            (CPSVal v₁))
           (CPSVal t''''))
           {k₂ = (λ v₁ t'''' →
          CPSApp
              (CPSVal
                (CPSFun
                 (λ t''' →
                    cpsTerm e₂
                    (λ v₃ t₄ →
                       CPSLet (CPSPlus (CPSVal v₁) (CPSVal v₃))
                       (λ v₄ → k₁ (CPSVar v₄) t₄))
                    (CPSVar t'''))))
          (CPSVal t''''))}
        (λ v t → sApp (sApp Subst≠ (sVal sVar=)) Subst≠) λ v t → rApp₁ (rBeta
        (sVal (sFun (λ x₈ →
        kSubst e₂
          (λ y →
             λ v₃ t₄ →
               CPSLet (CPSPlus (CPSVal y) (CPSVal v₃)) (λ v₄ → k₁ (CPSVar v₄) t₄))
          (λ x₉ t₄ → sLet (λ x₁₀ → Subst≠) (λ x₁₀ → sPlu (sVal sVar=) Subst≠))))))))))) ⟩
  CPSLet
    (CPSVal
     (CPSFun
      (λ z →
         CPSVal
         (CPSFun
          (λ z₁ →
             CPSVal
             (CPSFun
              (λ z₂ →
                 CPSLet
                 (CPSVal (CPSAppend refl t₁
                  (CPSCons x₂ (CPSVar z₁)
                   (CPSVar z₂))))
                 (λ z₃ →
                    cpsTerm (pcontext-plug p₃' (Val (Var z)))
                    (λ v₁ t'''' →
                       CPSApp
                       (CPSVal
                        (CPSFun
                         (λ t''' →
                            cpsTerm e₂
                            (λ v₃ t₄ →
                               CPSLet (CPSPlus (CPSVal v₁) (CPSVal v₃))
                               (λ v₄ → k₁ (CPSVar v₄) t₄))
                            (CPSVar t'''))))
                       (CPSVal t''''))
                    (CPSVar z₃)))))))))
    (λ x' → cpsTerm (e x') (CPSIdk x₁) CPSId)
  ⟶⟨ rLet₁ (rFun (λ x → rFun (λ x₅ → rFun (λ x₆ → rLet₂ (λ x₇ →
      correctCont (pcontext-plug p₃' (Val (Var x)))
        (λ v₁ t'''' →
           CPSApp
           (CPSVal
            (CPSFun
             (λ t''' →
                cpsTerm e₂
                (λ v₃ t₄ →
                   CPSLet (CPSPlus (CPSVal v₁) (CPSVal v₃))
                   (λ v₄ → k₁ (CPSVar v₄) t₄))
                (CPSVar t'''))))
           (CPSVal t''''))
           {k₂ = (λ v₁ t'''' →
               cpsTerm e₂
               (λ v₃ t₄ →
                  CPSLet (CPSPlus (CPSVal v₁) (CPSVal v₃))
                  (λ v₄ → k₁ (CPSVar v₄) t₄))
               t'''')}
        (λ v t → sApp (sVal (sFun (λ x₈ →
        kSubst e₂
          (λ y →
             λ v₃ t₄ →
               CPSLet (CPSPlus (CPSVal y) (CPSVal v₃)) (λ v₄ → k₁ (CPSVar v₄) t₄))
          (λ x₉ t₄ → sLet (λ x₁₀ → Subst≠) (λ x₁₀ → sPlu (sVal sVar=) Subst≠))))) Subst≠)
          λ v t → rBeta (tSubst e₂ (λ t₄ v₂ → sLet (λ x₈ → sch' t₄ (CPSVar x₈)) (λ x₈ → Subst≠)))))))) ⟩
  CPSLet
    (CPSVal
     (CPSFun
      (λ z →
         CPSVal
         (CPSFun
          (λ z₁ →
             CPSVal
             (CPSFun
              (λ z₂ →
                 CPSLet
                 (CPSVal (CPSAppend refl t₁
                  (CPSCons x₂ (CPSVar z₁)
                   (CPSVar z₂))))
                 (λ z₃ →
                    cpsTerm (pcontext-plug p₃' (Val (Var z)))
                    (λ v₁ t'''' →
                       cpsTerm e₂
                       (λ v₃ t₄ →
                          CPSLet (CPSPlus (CPSVal v₁) (CPSVal v₃))
                          (λ v₄ → k₁ (CPSVar v₄) t₄))
                       t'''')
                    (CPSVar z₃)))))))))
    (λ x' → cpsTerm (e x') (CPSIdk x₁) CPSId)
  ⟶⟨ rLet₁ (rFun (λ x → rFun (λ x₅ → rFun (λ x₆ → rLet₂ (λ x₇ →
      correctCont (pcontext-plug p₃' (Val (Var x)))
        (λ v₁ t'''' →
           cpsTerm e₂
           (λ v₃ t₄ →
              CPSLet (CPSPlus (CPSVal v₁) (CPSVal v₃))
              (λ v₄ → k₁ (CPSVar v₄) t₄))
           t'''')
           {k₂ = (λ v₁ →
                       cpsTerm e₂
                       (λ v₂ t₄ →
                          CPSLet (CPSPlus (CPSVal v₁) (CPSVal v₂))
                          (λ v₃ → k₁ (CPSVar v₃) t₄)))}
        (λ v t → kSubst e₂
                     (λ x₈ →
                        λ v₃ t₄ →
                          CPSLet (CPSPlus (CPSVal x₈) (CPSVal v₃))
                          (λ v₄ → k₁ (CPSVar v₄) t₄))
                     (λ x₈ t₄ → sLet (λ x₉ → Subst≠) (λ x₉ → sPlu (sVal sVar=) Subst≠)))
                     λ v t → correctCont e₂
                                 (λ v₃ t₄ →
                                    CPSLet (CPSPlus (CPSVal (cpsV v)) (CPSVal v₃))
                                    (λ v₄ → k₁ (CPSVar v₄) t₄))
                                    {k₂ = (λ v₂ t₄ →
          CPSLet (CPSPlus (CPSVal (cpsV v)) (CPSVal v₂))
          (λ v₃ → k₁ (CPSVar v₃) t₄))}
                                 (λ v₁ t₄ → sLet (λ x₈ → Subst≠) (λ x₈ → sPlu Subst≠ (sVal sVar=)))
                                 λ v₁ t₄ → rLet₂ (λ x₈ → r*Id)))))) ⟩
  CPSLet
    (CPSVal
     (CPSFun
      (λ z →
         CPSVal
         (CPSFun
          (λ z₁ →
             CPSVal
             (CPSFun
              (λ z₂ →
                 CPSLet
                 (CPSVal (CPSAppend refl t₁
                  (CPSCons x₂ (CPSVar z₁)
                   (CPSVar z₂))))
                 (λ z₃ →
                    cpsTerm (pcontext-plug p₃' (Val (Var z)))
                    (λ v₁ →
                       cpsTerm e₂
                       (λ v₂ t₄ →
                          CPSLet (CPSPlus (CPSVal v₁) (CPSVal v₂))
                          (λ v₃ → k₁ (CPSVar v₃) t₄)))
                    (CPSVar z₃)))))))))
    (λ x' → cpsTerm (e x') (CPSIdk x₁) CPSId)
  ⟵⟨ rLet₁ (rFun (λ x → rFun (λ x₅ → rFun (λ x₆ → rLet₂ (λ x₇ →
      correctCont (pcontext-plug p₃' (Val (Var x)))
        (λ v₁ →
           cpsTerm e₂
           (λ v₂ t₄ →
              CPSLet (CPSPlus (CPSVal v₁) (CPSVal v₂))
              (λ v₃ →
                 CPSApp (CPSVal (CPSFun (λ t''' → k₁ (CPSVar v₃) (CPSVar t'''))))
                 (CPSVal t₄))))
                 {k₂ = (λ v₁ →
          cpsTerm e₂
          (λ v₂ t₄ →
             CPSLet (CPSPlus (CPSVal v₁) (CPSVal v₂))
             (λ v₃ →
                k₁ (CPSVar v₃) t₄ )))}
        (λ v t → kSubst e₂
                     (λ x₈ →
                        λ v₂ t₄ →
                          CPSLet (CPSPlus (CPSVal x₈) (CPSVal v₂))
                          (λ v₃ →
                             CPSApp (CPSVal (CPSFun (λ t''' → k₁ (CPSVar v₃) (CPSVar t'''))))
                             (CPSVal t₄)))
                     (λ x₈ t₄ → sLet (λ x₉ → sApp Subst≠ Subst≠) (λ x₉ → sPlu (sVal sVar=) Subst≠)))
                     λ v t → correctCont e₂
                                 (λ v₂ t₄ →
                                    CPSLet (CPSPlus (CPSVal (cpsV v)) (CPSVal v₂))
                                    (λ v₃ →
                                       CPSApp (CPSVal (CPSFun (λ t''' → k₁ (CPSVar v₃) (CPSVar t'''))))
                                       (CPSVal t₄)))
                              {k₂ = (λ v₂ t₄ →
          CPSLet (CPSPlus (CPSVal (cpsV v)) (CPSVal v₂))
          (λ v₃ →
             k₁ (CPSVar v₃) t₄))}
                                 (λ v₁ t₄ → sLet (λ x₈ → sApp Subst≠ Subst≠)
                                 (λ x₈ → sPlu Subst≠ (sVal sVar=)))
                                 λ v₁ t₄ → rLet₂ (λ x₈ → rBeta (sch' t₄ (CPSVar x₈)))))))) ⟩
  CPSLet
    (CPSVal
     (CPSFun
      (λ z →
         CPSVal
         (CPSFun
          (λ z₁ →
             CPSVal
             (CPSFun
              (λ z₂ →
                 CPSLet
                 (CPSVal (CPSAppend refl t₁
                  (CPSCons x₂ (CPSVar z₁)
                   (CPSVar z₂))))
                 (λ z₃ →
                    cpsTerm (pcontext-plug p₃' (Val (Var z)))
                    (λ v₁ →
                       cpsTerm e₂
                       (λ v₂ t₄ →
                          CPSLet (CPSPlus (CPSVal v₁) (CPSVal v₂))
                          (λ v₃ →
                             CPSApp (CPSVal (CPSFun (λ t''' → k₁ (CPSVar v₃) (CPSVar t'''))))
                             (CPSVal t₄))))
                    (CPSVar z₃)))))))))
    (λ x' → cpsTerm (e x') (CPSIdk x₁) CPSId)
  ⟵⟨ rLet₁ (rFun (λ x → rFun (λ x₅ → rFun (λ x₆ → rLet₂ (λ x₇ →
      correctCont (pcontext-plug p₃' (Val (Var x)))
        (λ v₁ →
           cpsTerm e₂
           (λ v₂ t₄ →
              CPSLet (CPSPlus (CPSVal v₁) (CPSVal v₂))
              (λ v₃ →
                 CPSApp
                 (CPSApp
                  (CPSVal
                   (CPSFun
                    (λ v₄ → CPSVal (CPSFun (λ t''' → k₁ (CPSVar v₄) (CPSVar t'''))))))
                  (CPSVal (CPSVar v₃)))
                 (CPSVal t₄))))
                 {k₂ = (λ v₁ →
          cpsTerm e₂
          (λ v₂ t₄ →
             CPSLet (CPSPlus (CPSVal v₁) (CPSVal v₂))
             (λ v₃ →
                CPSApp
                (CPSVal (CPSFun (λ t''' → k₁ (CPSVar v₃) (CPSVar t'''))))
                 
                (CPSVal t₄))))}
        (λ v t → kSubst e₂
                     (λ x₈ →
                        λ v₂ t₄ →
                          CPSLet (CPSPlus (CPSVal x₈) (CPSVal v₂))
                          (λ v₃ →
                             CPSApp
                             (CPSApp
                              (CPSVal
                               (CPSFun
                                (λ v₄ → CPSVal (CPSFun (λ t''' → k₁ (CPSVar v₄) (CPSVar t'''))))))
                              (CPSVal (CPSVar v₃)))
                             (CPSVal t₄)))
                     (λ x₈ t₄ → sLet (λ x₉ → sApp Subst≠ Subst≠) (λ x₉ → sPlu (sVal sVar=) Subst≠)))
                     λ v t → correctCont e₂
                                 (λ v₂ t₄ →
                                    CPSLet (CPSPlus (CPSVal (cpsV v)) (CPSVal v₂))
                                    (λ v₃ →
                                       CPSApp
                                       (CPSApp
                                        (CPSVal
                                         (CPSFun
                                          (λ v₄ → CPSVal (CPSFun (λ t''' → k₁ (CPSVar v₄) (CPSVar t'''))))))
                                        (CPSVal (CPSVar v₃)))
                                       (CPSVal t₄)))
                                       {k₂ = (λ v₂ t₄ →
          CPSLet (CPSPlus (CPSVal (cpsV v)) (CPSVal v₂))
          (λ v₃ →
             CPSApp (CPSVal (CPSFun (λ t''' → k₁ (CPSVar v₃) (CPSVar t'''))))
             (CPSVal t₄)))}
                                 (λ v₁ t₄ → sLet (λ x₈ → sApp Subst≠ Subst≠)
                                 (λ x₈ → sPlu Subst≠ (sVal sVar=))) λ v₁ t₄ →
                                 rLet₂ (λ x₈ → rApp₁ (rBeta (sVal (sFun (λ x₉ → sch (CPSVar x₈) (CPSVar x₉))))))))))) ⟩
  CPSLet
    (CPSVal
     (CPSFun
      (λ z →
         CPSVal
         (CPSFun
          (λ z₁ →
             CPSVal
             (CPSFun
              (λ z₂ →
                 CPSLet
                 (CPSVal (CPSAppend refl t₁
                  (CPSCons x₂ (CPSVar z₁)
                   (CPSVar z₂))))
                 (λ z₃ →
                    cpsTerm (pcontext-plug p₃' (Val (Var z)))
                    (λ v₁ →
                       cpsTerm e₂
                       (λ v₂ t₄ →
                          CPSLet (CPSPlus (CPSVal v₁) (CPSVal v₂))
                          (λ v₃ →
                             CPSApp
                             (CPSApp
                              (CPSVal
                               (CPSFun
                                (λ v₄ → CPSVal (CPSFun (λ t''' → k₁ (CPSVar v₄) (CPSVar t'''))))))
                              (CPSVal (CPSVar v₃)))
                             (CPSVal t₄))))
                    (CPSVar z₃)))))))))
    (λ x' → cpsTerm (e x') (CPSIdk x₁) CPSId)
  ⟵⟨ rLet₁ (rFun (λ x → rFun (λ x₅ → rFun (λ x₆ → rLet₂ (λ x₇ → rBeta
      (tSubst (pcontext-plug p₃' (Val (Var x))) (λ t v₂ →
      tSubst e₂ (λ t₄ v₃ → sLet (λ x₈ → sApp Subst≠ (sVal sVar=)) (λ x₈ → Subst≠))))))))) ⟩
  CPSLet
    (CPSVal
     (CPSFun
      (λ z →
         CPSVal
         (CPSFun
          (λ z₁ →
             CPSVal
             (CPSFun
              (λ z₂ →
                 CPSLet
                 (CPSVal (CPSAppend refl t₁
                  (CPSCons x₂ (CPSVar z₁)
                   (CPSVar z₂))))
                 (λ z₃ →
                    CPSApp
                    (CPSVal
                     (CPSFun
                      (λ z₄ →
                         cpsTerm (pcontext-plug p₃' (Val (Var z)))
                         (λ v₁ →
                            cpsTerm e₂
                            (λ v₂ t₄ →
                               CPSLet (CPSPlus (CPSVal v₁) (CPSVal v₂))
                               (λ v₃ →
                                  CPSApp
                                  (CPSApp
                                   (CPSVal
                                    (CPSFun
                                     (λ v₄ → CPSVal (CPSFun (λ t''' → k₁ (CPSVar v₄) (CPSVar t'''))))))
                                   (CPSVal (CPSVar v₃)))
                                  (CPSVal t₄))))
                         (CPSVar z₄))))
                    (CPSVal (CPSVar z₃))))))))))
    (λ x' → cpsTerm (e x') (CPSIdk x₁) CPSId)
  ⟵⟨ rLet₁ (rFun (λ x → rFun (λ x₅ → rFun (λ x₆ → rLet₂ (λ x₇ → rApp₁ (rBeta
      (sVal (sFun (λ x₈ →
      kSubst (pcontext-plug p₃' (Val (Var x)))
        (λ y →
           λ v₁ →
             cpsTerm e₂
             (λ v₂ t₄ →
                CPSLet (CPSPlus (CPSVal v₁) (CPSVal v₂))
                (λ v₃ →
                   CPSApp (CPSApp (CPSVal y) (CPSVal (CPSVar v₃))) (CPSVal t₄))))
        (λ x₉ t → kSubst e₂
                      (λ x₁₀ →
                         λ v₂ t₄ →
                           CPSLet (CPSPlus (CPSVal x₉) (CPSVal v₂))
                           (λ v₃ →
                              CPSApp (CPSApp (CPSVal x₁₀) (CPSVal (CPSVar v₃))) (CPSVal t₄)))
                      (λ x₁₀ t₄ → sLet (λ x₁₁ → sApp (sApp (sVal sVar=) Subst≠) Subst≠) (λ x₁₁ → Subst≠)))))))))))) ⟩
  CPSLet
    (CPSVal
     (CPSFun
      (λ z →
         CPSVal
         (CPSFun
          (λ z₁ →
             CPSVal
             (CPSFun
              (λ z₂ →
                 CPSLet
                 (CPSVal (CPSAppend refl t₁
                  (CPSCons x₂ (CPSVar z₁)
                   (CPSVar z₂))))
                 (λ z₃ →
                    CPSApp
                    (CPSApp
                     (CPSVal
                      (CPSFun
                       (λ z₄ →
                          CPSVal
                          (CPSFun
                           (λ z₅ →
                              cpsTerm (pcontext-plug p₃' (Val (Var z)))
                              (λ v₁ →
                                 cpsTerm e₂
                                 (λ v₂ t₄ →
                                    CPSLet (CPSPlus (CPSVal v₁) (CPSVal v₂))
                                    (λ v₃ →
                                       CPSApp (CPSApp (CPSVal (CPSVar z₄)) (CPSVal (CPSVar v₃)))
                                       (CPSVal t₄))))
                              (CPSVar z₅))))))
                     (CPSVal
                      (CPSFun
                       (λ v₁ → CPSVal (CPSFun (λ t''' → k₁ (CPSVar v₁) (CPSVar t''')))))))
                    (CPSVal (CPSVar z₃))))))))))
    (λ x' → cpsTerm (e x') (CPSIdk x₁) CPSId)
  ⟵⟨ rLet₁ (rFun (λ x → rFun (λ x₅ → rFun (λ x₆ → rLet₂ (λ x₇ →
      rApp₁ (rApp₁ (rBeta (sVal (sFun (λ x₈ → sVal (sFun (λ x₉ → eSubst (subst-context p₃' (Var x))
      (λ {v₁} x₁₀ → kSubst′′ e₂
                        (λ x₁₁ →
                           λ v₂ t₄ →
                             CPSLet (CPSPlus (CPSVal (v₁ x₁₁)) (CPSVal v₂))
                             (λ v₃ →
                                CPSApp (CPSApp (CPSVal (CPSVar x₈)) (CPSVal (CPSVar v₃)))
                                (CPSVal t₄)))
                        (λ x₁₁ → sLet (λ x₁₂ → sApp Subst≠ Subst≠)
                        (λ x₁₂ → sPlu (sVal x₁₀) (sVal x₁₁)))))))))))))))) ⟩
  (CPSLet
       (CPSVal
        (CPSFun
         (λ v →
            CPSVal
            (CPSFun
             (λ k' →
                CPSVal
                (CPSFun
                 (λ t' →
                    CPSLet
                    (CPSVal (CPSAppend refl t₁
                     (CPSCons x₂ (CPSVar k')
                      (CPSVar t'))))
                    (λ t'' →
                       CPSApp
                       (CPSApp
                        (CPSApp
                         (CPSVal
                          (CPSFun
                           (λ x →
                              CPSVal
                              (CPSFun
                               (λ k'' →
                                  CPSVal
                                  (CPSFun
                                   (λ t''' →
                                      cpsTerm (pcontext-plug p₃' (Val (Var x)))
                                      (λ v₁ →
                                         cpsTerm e₂
                                         (λ v₂ t₄ →
                                            CPSLet (CPSPlus (CPSVal v₁) (CPSVal v₂))
                                            (λ v₃ →
                                               CPSApp
                                               (CPSApp (CPSVal (CPSVar k'')) (CPSVal (CPSVar v₃)))
                                               (CPSVal t₄))))
                                      (CPSVar t'''))))))))
                         (CPSVal (CPSVar v)))
                        (CPSVal
                         (CPSFun
                          (λ v₁ → CPSVal (CPSFun (λ t''' → k₁ (CPSVar v₁) (CPSVar t''')))))))
                       (CPSVal (CPSVar t''))))))))))
       (λ x' → cpsTerm (e x') (CPSIdk x₁) CPSId))

  ∎ -}
  
-- control-lemma  (Frame (App₁ e₂) p₁') (Frame (App₁ .e₂) p₃') x₁ x₂ x₃
--               (Frame {f₁ = (App₁ e₂)}{f₂ = (App₁ .e₂)} (App₁ .e₂) {c₁ = c₁}{c₂ = c₂} x₄) e k₁ t₁ k₂ sch sch' = begin
-- cpsreduce (cpsTerm (pcontext-plug p₁ (Control x₁ x₂ x₃ e)) k₁ tr)
--                (cpsTerm (App (Val (Fun (λ x → pcontext-plug p₃ (Val (Var x))))) (Control x₁ x₂ refl e)) k₁ tr)
control-lemma (Frame (Plus₂ v₁) p₁') (Frame (Plus₂ .v₁) p₃') x₁ x₂ x₃
              (Frame {f₁ = (Plus₂ v₁)}{f₂ = (Plus₂ .v₁)} (Plus₂ .v₁) {c₁ = c₁}{c₂ = c₂} x₄) e k₁ t₁ sch sch' = {!!}

{- begin

  (cpsTerm (pcontext-plug p₁' (Control x₁ x₂ x₃ e))
       (λ v₂ t₄ →
          CPSLet (CPSPlus (CPSVal (cpsV v₁)) (CPSVal v₂))
          (λ v → k₁ (CPSVar v) t₄))
       t₁)
  ⟶⟨ control-lemma p₁' p₃' x₁ x₂ x₃ x₄ e
       (λ v₂ t₄ →
          CPSLet (CPSPlus (CPSVal (cpsV v₁)) (CPSVal v₂))
          (λ v → k₁ (CPSVar v) t₄))
       t₁ (λ v t → sLet (λ x → Subst≠) (λ x → sPlu Subst≠ (sVal sVar=)))
       (λ t v₂ → sLet (λ x → sch' t (CPSVar x)) (λ x → Subst≠)) ⟩
  cpsTerm
    (App (Val (Fun (λ x → pcontext-plug p₃' (Val (Var x)))))
     (Control x₁ x₂ refl e))
    (λ v₂ t₄ →
       CPSLet (CPSPlus (CPSVal (cpsV v₁)) (CPSVal v₂))
       (λ v → k₁ (CPSVar v) t₄))
    t₁
  ≡⟨ refl ⟩
  (CPSLet
       (CPSVal
        (CPSFun
         (λ v →
            CPSVal
            (CPSFun
             (λ k' →
                CPSVal
                (CPSFun
                 (λ t' →
                    CPSLet
                    (CPSVal (CPSAppend refl t₁
                     (CPSCons x₂ (CPSVar k')
                      (CPSVar t'))))
                    (λ t'' →
                       CPSApp
                       (CPSApp
                        (CPSApp
                         (CPSVal
                          (CPSFun
                           (λ x →
                              CPSVal
                              (CPSFun
                               (λ k'' →
                                  CPSVal
                                  (CPSFun
                                   (λ t''' →
                                      cpsTerm (pcontext-plug p₃' (Val (Var x)))
                                      (λ v₂ t'''' →
                                         CPSApp (CPSApp (CPSVal (CPSVar k'')) (CPSVal v₂))
                                         (CPSVal t''''))
                                      (CPSVar t'''))))))))
                         (CPSVal (CPSVar v)))
                        (CPSVal
                         (CPSFun
                          (λ v₂ →
                             CPSVal
                             (CPSFun
                              (λ t''' →
                                 CPSLet (CPSPlus (CPSVal (cpsV v₁)) (CPSVal (CPSVar v₂)))
                                 (λ v₃ → k₁ (CPSVar v₃) (CPSVar t'''))))))))
                       (CPSVal (CPSVar t''))))))))))
       (λ x' → cpsTerm (e x') (CPSIdk x₁) CPSId))
  ⟶⟨ rLet₁ (rFun (λ x → rFun (λ x₅ → rFun (λ x₆ → rLet₂ (λ x₇ → rApp₁ (rApp₁ (rBeta
      (sVal (sFun (λ x₈ → sVal (sFun (λ x₉ →
      eSubst (subst-context p₃' (Var x))
      (λ x₁₀ → sApp (sApp Subst≠ (sVal x₁₀)) Subst≠))))))))))))) ⟩
  CPSLet
    (CPSVal
     (CPSFun
      (λ z →
         CPSVal
         (CPSFun
          (λ z₁ →
             CPSVal
             (CPSFun
              (λ z₂ →
                 CPSLet
                 (CPSVal (CPSAppend refl t₁
                  (CPSCons x₂ (CPSVar z₁)
                   (CPSVar z₂))))
                 (λ z₃ →
                    CPSApp
                    (CPSApp
                     (CPSVal
                      (CPSFun
                       (λ z₄ →
                          CPSVal
                          (CPSFun
                           (λ z₅ →
                              cpsTerm (pcontext-plug p₃' (Val (Var z)))
                              (λ v₂ t'''' →
                                 CPSApp (CPSApp (CPSVal (CPSVar z₄)) (CPSVal v₂)) (CPSVal t''''))
                              (CPSVar z₅))))))
                     (CPSVal
                      (CPSFun
                       (λ v₂ →
                          CPSVal
                          (CPSFun
                           (λ t''' →
                              CPSLet (CPSPlus (CPSVal (cpsV v₁)) (CPSVal (CPSVar v₂)))
                              (λ v₃ → k₁ (CPSVar v₃) (CPSVar t'''))))))))
                    (CPSVal (CPSVar z₃))))))))))
    (λ x' → cpsTerm (e x') (CPSIdk x₁) CPSId)
  ⟶⟨ rLet₁ (rFun (λ x → rFun (λ x₅ → rFun (λ x₆ → rLet₂ (λ x₇ → rApp₁ (rBeta
      (sVal (sFun (λ x₈ →
      kSubst (pcontext-plug p₃' (Val (Var x)))
        (λ y →
           λ v₂ t'''' → CPSApp (CPSApp (CPSVal y) (CPSVal v₂)) (CPSVal t''''))
        (λ x₉ t → sApp (sApp (sVal sVar=) Subst≠) Subst≠)))))))))) ⟩
  CPSLet
    (CPSVal
     (CPSFun
      (λ z →
         CPSVal
         (CPSFun
          (λ z₁ →
             CPSVal
             (CPSFun
              (λ z₂ →
                 CPSLet
                 (CPSVal (CPSAppend refl t₁
                  (CPSCons x₂ (CPSVar z₁)
                   (CPSVar z₂))))
                 (λ z₃ →
                    CPSApp
                    (CPSVal
                     (CPSFun
                      (λ z₄ →
                         cpsTerm (pcontext-plug p₃' (Val (Var z)))
                         (λ v₂ t'''' →
                            CPSApp
                            (CPSApp
                             (CPSVal
                              (CPSFun
                               (λ v₃ →
                                  CPSVal
                                  (CPSFun
                                   (λ t''' →
                                      CPSLet (CPSPlus (CPSVal (cpsV v₁)) (CPSVal (CPSVar v₃)))
                                      (λ v₄ → k₁ (CPSVar v₄) (CPSVar t''')))))))
                             (CPSVal v₂))
                            (CPSVal t''''))
                         (CPSVar z₄))))
                    (CPSVal (CPSVar z₃))))))))))
    (λ x' → cpsTerm (e x') (CPSIdk x₁) CPSId)
  ⟶⟨ rLet₁ (rFun (λ x → rFun (λ x₅ → rFun (λ x₆ → rLet₂ (λ x₇ → rBeta
      (tSubst (pcontext-plug p₃' (Val (Var x))) (λ t v₂ → sApp Subst≠ (sVal sVar=)))))))) ⟩
  CPSLet
    (CPSVal
     (CPSFun
      (λ z →
         CPSVal
         (CPSFun
          (λ z₁ →
             CPSVal
             (CPSFun
              (λ z₂ →
                 CPSLet
                 (CPSVal (CPSAppend refl t₁
                  (CPSCons x₂ (CPSVar z₁)
                   (CPSVar z₂))))
                 (λ z₃ →
                    cpsTerm (pcontext-plug p₃' (Val (Var z)))
                    (λ v₂ t'''' →
                       CPSApp
                       (CPSApp
                        (CPSVal
                         (CPSFun
                          (λ v₃ →
                             CPSVal
                             (CPSFun
                              (λ t''' →
                                 CPSLet (CPSPlus (CPSVal (cpsV v₁)) (CPSVal (CPSVar v₃)))
                                 (λ v₄ → k₁ (CPSVar v₄) (CPSVar t''')))))))
                        (CPSVal v₂))
                       (CPSVal t''''))
                    (CPSVar z₃)))))))))
    (λ x' → cpsTerm (e x') (CPSIdk x₁) CPSId)
  ⟶⟨ rLet₁ (rFun (λ x → rFun (λ x₅ → rFun (λ x₆ → rLet₂ (λ x₇ →
      correctCont (pcontext-plug p₃' (Val (Var x)))
        (λ v₂ t'''' →
           CPSApp
           (CPSApp
            (CPSVal
             (CPSFun
              (λ v₃ →
                 CPSVal
                 (CPSFun
                  (λ t''' →
                     CPSLet (CPSPlus (CPSVal (cpsV v₁)) (CPSVal (CPSVar v₃)))
                     (λ v₄ → k₁ (CPSVar v₄) (CPSVar t''')))))))
            (CPSVal v₂))
           (CPSVal t''''))
           {k₂ = (λ v₂ t'''' →
             CPSApp
               (CPSVal
                (CPSFun
                 (λ t''' →
                    CPSLet (CPSPlus (CPSVal (cpsV v₁)) (CPSVal v₂))
                    (λ v₄ → k₁ (CPSVar v₄) (CPSVar t''')))))
                    (CPSVal t''''))}
        (λ v t → sApp (sApp Subst≠ (sVal sVar=)) Subst≠)
        λ v t → rApp₁ (rBeta (sVal (sFun (λ x₈ → sLet (λ x₉ → Subst≠)
        (λ x₉ → sPlu Subst≠ (sVal sVar=))))))))))) ⟩
  CPSLet
    (CPSVal
     (CPSFun
      (λ z →
         CPSVal
         (CPSFun
          (λ z₁ →
             CPSVal
             (CPSFun
              (λ z₂ →
                 CPSLet
                 (CPSVal (CPSAppend refl t₁
                  (CPSCons x₂ (CPSVar z₁)
                   (CPSVar z₂))))
                 (λ z₃ →
                    cpsTerm (pcontext-plug p₃' (Val (Var z)))
                    (λ v₂ t'''' →
                       CPSApp
                       (CPSVal
                        (CPSFun
                         (λ t''' →
                            CPSLet (CPSPlus (CPSVal (cpsV v₁)) (CPSVal v₂))
                            (λ v₄ → k₁ (CPSVar v₄) (CPSVar t''')))))
                       (CPSVal t''''))
                    (CPSVar z₃)))))))))
    (λ x' → cpsTerm (e x') (CPSIdk x₁) CPSId)
  ⟶⟨ rLet₁ (rFun (λ x → rFun (λ x₅ → rFun (λ x₆ → rLet₂ (λ x₇ →
      correctCont (pcontext-plug p₃' (Val (Var x)))
        (λ v₂ t'''' →
           CPSApp
           (CPSVal
            (CPSFun
             (λ t''' →
                CPSLet (CPSPlus (CPSVal (cpsV v₁)) (CPSVal v₂))
                (λ v₄ → k₁ (CPSVar v₄) (CPSVar t''')))))
           (CPSVal t''''))
           {k₂ = (λ v₂ t'''' →
               CPSLet (CPSPlus (CPSVal (cpsV v₁)) (CPSVal v₂))
               (λ v₄ → k₁ (CPSVar v₄) t''''))}
        (λ v t → sApp (sVal (sFun (λ x₈ → sLet (λ x₉ → Subst≠) (λ x₉ → sPlu Subst≠ (sVal sVar=))))) Subst≠)
        λ v t → rBeta (sLet (λ x₈ → sch' t (CPSVar x₈)) (λ x₈ → Subst≠))))))) ⟩
  CPSLet
    (CPSVal
     (CPSFun
      (λ z →
         CPSVal
         (CPSFun
          (λ z₁ →
             CPSVal
             (CPSFun
              (λ z₂ →
                 CPSLet
                 (CPSVal (CPSAppend refl t₁
                  (CPSCons x₂ (CPSVar z₁)
                   (CPSVar z₂))))
                 (λ z₃ →
                    cpsTerm (pcontext-plug p₃' (Val (Var z)))
                    (λ v₂ t'''' →
                       CPSLet (CPSPlus (CPSVal (cpsV v₁)) (CPSVal v₂))
                       (λ v₄ → k₁ (CPSVar v₄) t''''))
                    (CPSVar z₃)))))))))
    (λ x' → cpsTerm (e x') (CPSIdk x₁) CPSId)
  ≡⟨ refl ⟩
  CPSLet
    (CPSVal
     (CPSFun
      (λ z →
         CPSVal
         (CPSFun
          (λ z₁ →
             CPSVal
             (CPSFun
              (λ z₂ →
                 CPSLet
                 (CPSVal (CPSAppend refl t₁
                  (CPSCons x₂ (CPSVar z₁)
                   (CPSVar z₂))))
                 (λ z₃ →
                    cpsTerm (pcontext-plug p₃' (Val (Var z)))
                    (λ v₂ t₄ →
                       CPSLet (CPSPlus (CPSVal (cpsV v₁)) (CPSVal v₂))
                       (λ v₃ → k₁ (CPSVar v₃) t₄))
                    (CPSVar z₃)))))))))
    (λ x' → cpsTerm (e x') (CPSIdk x₁) CPSId)
  ⟵⟨ rLet₁ (rFun (λ x → rFun (λ x₅ → rFun (λ x₆ → rLet₂ (λ x₇ →
      correctCont (pcontext-plug p₃' (Val (Var x)))
        (λ v₂ t₄ →
           CPSLet (CPSPlus (CPSVal (cpsV v₁)) (CPSVal v₂))
           (λ v₃ →
              CPSApp (CPSVal (CPSFun (λ t''' → k₁ (CPSVar v₃) (CPSVar t'''))))
              (CPSVal t₄)))
              {k₂ = (λ v₂ t₄ →
          CPSLet (CPSPlus (CPSVal (cpsV v₁)) (CPSVal v₂))
          (λ v₃ → k₁ (CPSVar v₃) t₄))}
        (λ v t → sLet (λ x₈ → sApp Subst≠ Subst≠) (λ x₈ → sPlu Subst≠ (sVal sVar=)))
        λ v t → rLet₂ (λ x₈ → rBeta (sch' t (CPSVar x₈)))))))) ⟩
  CPSLet
    (CPSVal
     (CPSFun
      (λ z →
         CPSVal
         (CPSFun
          (λ z₁ →
             CPSVal
             (CPSFun
              (λ z₂ →
                 CPSLet
                 (CPSVal (CPSAppend refl t₁
                  (CPSCons x₂ (CPSVar z₁)
                   (CPSVar z₂))))
                 (λ z₃ →
                    cpsTerm (pcontext-plug p₃' (Val (Var z)))
                    (λ v₂ t₄ →
                       CPSLet (CPSPlus (CPSVal (cpsV v₁)) (CPSVal v₂))
                       (λ v₃ →
                          CPSApp (CPSVal (CPSFun (λ t''' → k₁ (CPSVar v₃) (CPSVar t'''))))
                          (CPSVal t₄)))
                    (CPSVar z₃)))))))))
    (λ x' → cpsTerm (e x') (CPSIdk x₁) CPSId)
  ⟵⟨ rLet₁ (rFun (λ x → rFun (λ x₅ → rFun (λ x₆ → rLet₂ (λ x₇ →
      correctCont (pcontext-plug p₃' (Val (Var x)))
        (λ v₂ t₄ →
           CPSLet (CPSPlus (CPSVal (cpsV v₁)) (CPSVal v₂))
           (λ v₃ →
              CPSApp
              (CPSApp
               (CPSVal
                (CPSFun
                 (λ v₄ → CPSVal (CPSFun (λ t''' → k₁ (CPSVar v₄) (CPSVar t'''))))))
               (CPSVal (CPSVar v₃)))
              (CPSVal t₄)))
              {k₂ = (λ v₂ t₄ →
          CPSLet (CPSPlus (CPSVal (cpsV v₁)) (CPSVal v₂))
          (λ v₃ →
             CPSApp
              (CPSVal (CPSFun (λ t''' → k₁ (CPSVar v₃) (CPSVar t'''))))
              (CPSVal t₄)))}
        (λ v t → sLet (λ x₈ → sApp Subst≠ Subst≠) (λ x₈ → sPlu Subst≠ (sVal sVar=)))
        λ v t → rLet₂ (λ x₈ → rApp₁ (rBeta (sVal (sFun (λ x₉ → sch (CPSVar x₈) (CPSVar x₉))))))))))) ⟩
  CPSLet
    (CPSVal
     (CPSFun
      (λ z →
         CPSVal
         (CPSFun
          (λ z₁ →
             CPSVal
             (CPSFun
              (λ z₂ →
                 CPSLet
                 (CPSVal (CPSAppend refl t₁
                  (CPSCons x₂ (CPSVar z₁)
                   (CPSVar z₂))))
                 (λ z₃ →
                    cpsTerm (pcontext-plug p₃' (Val (Var z)))
                    (λ v₂ t₄ →
                       CPSLet (CPSPlus (CPSVal (cpsV v₁)) (CPSVal v₂))
                       (λ v₃ →
                          CPSApp
                          (CPSApp
                           (CPSVal
                            (CPSFun
                             (λ v₄ → CPSVal (CPSFun (λ t''' → k₁ (CPSVar v₄) (CPSVar t'''))))))
                           (CPSVal (CPSVar v₃)))
                          (CPSVal t₄)))
                    (CPSVar z₃)))))))))
    (λ x' → cpsTerm (e x') (CPSIdk x₁) CPSId)
  ⟵⟨ rLet₁ (rFun (λ x → rFun (λ x₅ → rFun (λ x₆ → rLet₂ (λ x₇ → rBeta
      (tSubst (pcontext-plug p₃' (Val (Var x)))
      (λ t v₂ → sLet (λ x₈ → sApp Subst≠ (sVal sVar=)) (λ x₈ → Subst≠)))))))) ⟩
  CPSLet
    (CPSVal
     (CPSFun
      (λ z →
         CPSVal
         (CPSFun
          (λ z₁ →
             CPSVal
             (CPSFun
              (λ z₂ →
                 CPSLet
                 (CPSVal (CPSAppend refl t₁
                  (CPSCons x₂ (CPSVar z₁)
                   (CPSVar z₂))))
                 (λ z₃ →
                    CPSApp
                    (CPSVal
                     (CPSFun
                      (λ z₄ →
                         cpsTerm (pcontext-plug p₃' (Val (Var z)))
                         (λ v₂ t₄ →
                            CPSLet (CPSPlus (CPSVal (cpsV v₁)) (CPSVal v₂))
                            (λ v₃ →
                               CPSApp
                               (CPSApp
                                (CPSVal
                                 (CPSFun
                                  (λ v₄ → CPSVal (CPSFun (λ t''' → k₁ (CPSVar v₄) (CPSVar t'''))))))
                                (CPSVal (CPSVar v₃)))
                               (CPSVal t₄)))
                         (CPSVar z₄))))
                    (CPSVal (CPSVar z₃))))))))))
    (λ x' → cpsTerm (e x') (CPSIdk x₁) CPSId)
  ⟵⟨ rLet₁ (rFun (λ x → rFun (λ x₅ → rFun (λ x₆ → rLet₂ (λ x₇ → rApp₁ (rBeta
      (sVal (sFun (λ x₈ →
      kSubst (pcontext-plug p₃' (Val (Var x)))
        (λ y →
           λ v₂ t₄ →
             CPSLet (CPSPlus (CPSVal (cpsV v₁)) (CPSVal v₂))
             (λ v₃ →
                CPSApp (CPSApp (CPSVal y) (CPSVal (CPSVar v₃))) (CPSVal t₄)))
        (λ x₉ t → sLet (λ x₁₀ → sApp (sApp (sVal sVar=) Subst≠) Subst≠) (λ x₁₀ → Subst≠))))))))))) ⟩
  CPSLet
    (CPSVal
     (CPSFun
      (λ z →
         CPSVal
         (CPSFun
          (λ z₁ →
             CPSVal
             (CPSFun
              (λ z₂ →
                 CPSLet
                 (CPSVal (CPSAppend refl t₁
                  (CPSCons x₂ (CPSVar z₁)
                   (CPSVar z₂))))
                 (λ z₃ →
                    CPSApp
                    (CPSApp
                     (CPSVal
                      (CPSFun
                       (λ z₄ →
                          CPSVal
                          (CPSFun
                           (λ z₅ →
                              cpsTerm (pcontext-plug p₃' (Val (Var z)))
                              (λ v₂ t₄ →
                                 CPSLet (CPSPlus (CPSVal (cpsV v₁)) (CPSVal v₂))
                                 (λ v₃ →
                                    CPSApp (CPSApp (CPSVal (CPSVar z₄)) (CPSVal (CPSVar v₃)))
                                    (CPSVal t₄)))
                              (CPSVar z₅))))))
                     (CPSVal
                      (CPSFun
                       (λ v₂ → CPSVal (CPSFun (λ t''' → k₁ (CPSVar v₂) (CPSVar t''')))))))
                    (CPSVal (CPSVar z₃))))))))))
    (λ x' → cpsTerm (e x') (CPSIdk x₁) CPSId)
  ⟵⟨ rLet₁ (rFun (λ x → rFun (λ x₅ → rFun (λ x₆ → rLet₂ (λ x₇ → rApp₁ (rApp₁ (rBeta
      (sVal (sFun (λ x₈ → sVal (sFun (λ x₉ → eSubst (subst-context p₃' (Var x))
      (λ x₁₀ → sLet (λ x₁₁ → sApp Subst≠ Subst≠)
      (λ x₁₁ → sPlu Subst≠ (sVal x₁₀))))))))))))))) ⟩
  (CPSLet
       (CPSVal
        (CPSFun
         (λ v →
            CPSVal
            (CPSFun
             (λ k' →
                CPSVal
                (CPSFun
                 (λ t' →
                    CPSLet
                    (CPSVal (CPSAppend refl t₁
                     (CPSCons x₂ (CPSVar k')
                      (CPSVar t'))))
                    (λ t'' →
                       CPSApp
                       (CPSApp
                        (CPSApp
                         (CPSVal
                          (CPSFun
                           (λ x →
                              CPSVal
                              (CPSFun
                               (λ k'' →
                                  CPSVal
                                  (CPSFun
                                   (λ t''' →
                                      cpsTerm (pcontext-plug p₃' (Val (Var x)))
                                      (λ v₂ t₄ →
                                         CPSLet (CPSPlus (CPSVal (cpsV v₁)) (CPSVal v₂))
                                         (λ v₃ →
                                            CPSApp
                                            (CPSApp (CPSVal (CPSVar k'')) (CPSVal (CPSVar v₃)))
                                            (CPSVal t₄)))
                                      (CPSVar t'''))))))))
                         (CPSVal (CPSVar v)))
                        (CPSVal
                         (CPSFun
                          (λ v₂ → CPSVal (CPSFun (λ t''' → k₁ (CPSVar v₂) (CPSVar t''')))))))
                       (CPSVal (CPSVar t''))))))))))
       (λ x' → cpsTerm (e x') (CPSIdk x₁) CPSId))
  ∎ -}


{-
aux₄-con : ∀ {var} {μ₄} {x₅} {α₂} {μ₀} {μ₃} 
         {μ₁} 
        {c₂ : compatible (x₅ ⇒ α₂ , μ₀) μ₁ μ₃}
        {x₂ : compatible (x₅ ⇒ α₂ , μ₀) μ₀ μ₄}
        {x₃ : compatible (x₅ ⇒ α₂ , μ₄) μ₃ μ₃}
        (k : var (cpsT x₅ ⇛ (cpsM μ₄ ⇛ cpsT α₂)))
        (t : var (cpsM (x₅ ⇒ α₂ , μ₀)))
        (z : var (cpsM μ₁)) →
      cpsreduce {var}
      (CPSVal
       (CPSCons c₂ (CPSCons (refl , refl , x₂) (CPSVar k) (CPSVar t))
       (CPSVar z) ))
      (CPSVal
       (CPSCons x₃ (CPSVar k)
        (CPSCons c₂ (CPSVar t) (CPSVar z))))

aux₄-con {μ₁ = ∙}{c₂ = refl}{x₂}{refl , refl , snd} k t z rewrite compatible-equal x₂ snd = begin
  (CPSVal
       (CPSCons refl (CPSCons (refl , refl , snd) (CPSVar k) (CPSVar t))
        (CPSVar z)))

  ⟶⟨ rConsid₂ ⟩
  CPSVal (CPSCons (refl , refl , snd) (CPSVar k) (CPSVar t))
  ⟵⟨ rCon₂ rConsid₂ ⟩
  (CPSVal
       (CPSCons (refl , refl , snd) (CPSVar k)
        (CPSCons refl (CPSVar t) (CPSVar z))))

  ∎

{- aux₄-con {μ₄ = ∙} {μ₃ = x₄ ⇒ x₅ , μ₃} {μ₁ = x ⇒ x₁ , μ₁} {refl , refl , snd} {x₂} {refl , refl , snd₁} k t z = {!!}
aux₄-con {μ₄ = x₃ ⇒ x₆ , μ₄} {μ₃ = x₄ ⇒ x₅ , μ₃} {μ₁ = x ⇒ x₁ , μ₁} {refl , refl , snd} {x₂} {refl , refl , snd₁} k t z = begin
  (CPSVal
       (CPSCons (refl , refl , snd)
        (CPSCons (refl , refl , x₂) (CPSVar k) (CPSVar t)) (CPSVar z)))

  ⟶⟨ rCon₁ rConst ⟩
  CPSVal
    (CPSCons (refl , refl , snd)
     (CPSFun
      (λ v →
         CPSVal
         (CPSFun
          (λ t' →
             CPSApp (CPSApp (CPSVal (CPSVar k)) (CPSVal (CPSVar v)))
             (CPSVal (CPSCons x₂ (CPSVar t) (CPSVar t')))))))
     (CPSVar z))
  ⟶⟨ rConst ⟩
  CPSVal
    (CPSFun
     (λ v →
        CPSVal
        (CPSFun
         (λ t' →
            CPSApp
            (CPSApp
             (CPSVal
              (CPSFun
               (λ v₁ →
                  CPSVal
                  (CPSFun
                   (λ t'' →
                      CPSApp (CPSApp (CPSVal (CPSVar k)) (CPSVal (CPSVar v₁)))
                      (CPSVal (CPSCons x₂ (CPSVar t) (CPSVar t''))))))))
             (CPSVal (CPSVar v)))
            (CPSVal (CPSCons snd (CPSVar z) (CPSVar t')))))))

  ⟶⟨ rFun (λ x₃ → rFun (λ x₆ → rApp₁ (rBeta (sVal (sFun (λ x₇ → sApp (sApp Subst≠ (sVal sVar=)) Subst≠)))))) ⟩
  CPSVal
    (CPSFun
     (λ z₁ →
        CPSVal
        (CPSFun
         (λ z₂ →
            CPSApp
            (CPSVal
             (CPSFun
              (λ z₃ →
                 CPSApp (CPSApp (CPSVal (CPSVar k)) (CPSVal (CPSVar z₁)))
                 (CPSVal (CPSCons x₂ (CPSVar t) (CPSVar z₃))))))
            (CPSVal (CPSCons snd (CPSVar z) (CPSVar z₂)))))))
  ⟶⟨ rFun (λ x₃ → rFun (λ x₆ → rBeta (sApp Subst≠ (sVal (sCon SubstV≠ sVar=))))) ⟩
  CPSVal
    (CPSFun
     (λ z₁ →
        CPSVal
        (CPSFun
         (λ z₂ →
            CPSApp (CPSApp (CPSVal (CPSVar k)) (CPSVal (CPSVar z₁)))
            (CPSVal (CPSCons x₂ (CPSVar t) (CPSCons snd (CPSVar z) (CPSVar z₂))))))))

  ⟶⟨ rFun (λ x₇ → rFun (λ x₈ → rApp₂ {!rConst!})) ⟩
  {!!}
  ⟶⟨ {!!} ⟩
  {!!}
  ⟵⟨ {!!} ⟩
  {!!}
  ⟵⟨ rConst ⟩
  (CPSVal
       (CPSCons (refl , refl , snd₁) (CPSVar k)
        (CPSCons (refl , refl , snd) (CPSVar t) (CPSVar z))))

  ∎ -}
aux₄-con  {μ₃ = x₄ ⇒ x₅ , μ₃} {μ₁ = x ⇒ x₁ , μ₁} {refl , refl , snd} {x₂} {refl , refl , snd₁} k t z = begin

  (CPSVal
       (CPSCons (refl , refl , snd)
        (CPSCons (refl , refl , x₂) (CPSVar k) (CPSVar t)) (CPSVar z)))

  ⟶⟨ rCon₁ rConst ⟩
  CPSVal
    (CPSCons (refl , refl , snd)
     (CPSFun
      (λ v →
         CPSVal
         (CPSFun
          (λ t' →
             CPSApp (CPSApp (CPSVal (CPSVar k)) (CPSVal (CPSVar v)))
             (CPSVal (CPSCons x₂ (CPSVar t) (CPSVar t')))))))
     (CPSVar z))
  ⟶⟨ rConst ⟩
  CPSVal
    (CPSFun
     (λ v →
        CPSVal
        (CPSFun
         (λ t' →
            CPSApp
            (CPSApp
             (CPSVal
              (CPSFun
               (λ v₁ →
                  CPSVal
                  (CPSFun
                   (λ t'' →
                      CPSApp (CPSApp (CPSVal (CPSVar k)) (CPSVal (CPSVar v₁)))
                      (CPSVal (CPSCons x₂ (CPSVar t) (CPSVar t''))))))))
             (CPSVal (CPSVar v)))
            (CPSVal (CPSCons snd (CPSVar z) (CPSVar t')))))))
  ⟶⟨ rFun (λ x₃ → rFun (λ x₆ → rApp₁ (rBeta (sVal (sFun (λ x₇ → sApp (sApp Subst≠ (sVal sVar=)) Subst≠)))))) ⟩
  CPSVal
    (CPSFun
     (λ z₁ →
        CPSVal
        (CPSFun
         (λ z₂ →
            CPSApp
            (CPSVal
             (CPSFun
              (λ z₃ →
                 CPSApp (CPSApp (CPSVal (CPSVar k)) (CPSVal (CPSVar z₁)))
                 (CPSVal (CPSCons x₂ (CPSVar t) (CPSVar z₃))))))
            (CPSVal (CPSCons snd (CPSVar z) (CPSVar z₂)))))))
  ⟶⟨ rFun (λ x₃ → rFun (λ x₆ → rBeta (sApp Subst≠ (sVal (sCon SubstV≠ sVar=))))) ⟩
  CPSVal
    (CPSFun
     (λ z₁ →
        CPSVal
        (CPSFun
         (λ z₂ →
            CPSApp (CPSApp (CPSVal (CPSVar k)) (CPSVal (CPSVar z₁)))
            (CPSVal (CPSCons x₂ (CPSVar t) (CPSCons snd (CPSVar z) (CPSVar z₂))))))))
  ⟵⟨ rFun (λ x₃ → rFun (λ x₆ → rApp₂ {!aux₄-con  t z x₆!})) ⟩
  CPSVal
    (CPSFun
     (λ v →
        CPSVal
        (CPSFun
         (λ t' →
            CPSApp (CPSApp (CPSVal (CPSVar k)) (CPSVal (CPSVar v)))
            (CPSVal
             (CPSCons snd₁ (CPSCons (refl , refl , snd) (CPSVar t) (CPSVar z))
              (CPSVar t')))))))
  ⟵⟨ rConst ⟩
  (CPSVal
       (CPSCons (refl , refl , snd₁) (CPSVar k)
        (CPSCons (refl , refl , snd) (CPSVar t) (CPSVar z))))

  ∎ -}
-- aux₄-con {μ₁ = x ⇒ x₁ , μ₁}{c₂}{x₂}{x₃} k t z = begin
--   (CPSVal
--        (CPSCons c₂ (CPSCons (refl , refl , x₂) (CPSVar k) (CPSVar t)) z))

--   ⟶⟨ rCon₁ rConst ⟩
--   CPSVal
--     (CPSCons c₂
--      (CPSFun
--       (λ v →
--          CPSVal
--          (CPSFun
--           (λ t' →
--              CPSApp (CPSApp (CPSVal (CPSVar k)) (CPSVal (CPSVar v)))
--              (CPSVal (CPSCons x₂ (CPSVar t) (CPSVar t')))))))
--      z)
--   ⟶⟨ {!rConst!} ⟩
--    {!!}
--   ⟵⟨ rCon₂ {!rConst!} ⟩
--   (CPSVal (CPSCons x₃ (CPSVar k) (CPSCons c₂ (CPSVar t) z)))
--   ∎

-- aux₄-p : ∀ {var : cpstyp → Set}{μ₄ μ₃ : trail}
--          {α} {x₄} {x₅} {α₁} {α₂}{τ₁}{μα}{β}
--          {μ₀}
         
--          -- (e : term[ var ∘ cpsT ] x₄ ⟨ μ₃ ⟩ α₁ ⟨ x₅ ⇒ α₂ , μ₀ ⟩ α)
--          (p : pcontext[ var ∘ cpsT , τ₁ ⟨ []{μα} ⟩ β ⟨ μα ⟩ β ] x₄ ⟨ μ₃ ⟩ α₁ ⟨ x₅ ⇒ α₂ , μ₀ ⟩ α)
--          (v : (var ∘ cpsT) τ₁)
--          {x₂ : compatible (x₅ ⇒ α₂ , μ₀) μ₀ μ₄}
--          {x₃ : compatible (x₅ ⇒ α₂ , μ₄) μ₃ μ₃}
--          (κ : cpsvalue[ var ] (cpsT x₄) →  cpsvalue[ var ] (cpsM μ₃) →
--               cpsterm[ var ] (cpsT α₁))
--          (k : var (cpsT x₅ ⇛ (cpsM μ₄ ⇛ cpsT α₂)))
--          (t : var (cpsM (x₅ ⇒ α₂ , μ₀))) →
--        cpsreduce {var}
--        (cpsTerm (pcontext-plug p (Val (Var v)))
--        (λ v t' →
--            κ v t')
--             (CPSCons (refl , (refl , x₂)) (CPSVar k) (CPSVar t)))
--        (cpsTerm (pcontext-plug p (Val (Var v)))
--         (λ v t' →
--            κ v (CPSCons x₃ (CPSVar k) t'))
--         (CPSVar t))


-- aux₄-p Hole v κ k t = {!!}
-- aux₄-p (Frame (App₁ e₂) p) v {x₂}{x₃} κ₂ k t  = begin
--   (cpsTerm (pcontext-plug p (Val (Var v)))
--        (λ v₁ →
--           cpsTerm e₂
--           (λ v₂ t₂ →
--              CPSApp
--              (CPSApp (CPSApp (CPSVal v₁) (CPSVal v₂))
--               (CPSVal
--                (CPSFun
--                 (λ v₃ → CPSVal (CPSFun (λ t'' → κ₂ (CPSVar v₃) (CPSVar t'')))))))
--              (CPSVal t₂)))
--        (CPSCons (refl , refl , x₂) (CPSVar k) (CPSVar t)))

--   ⟶⟨ aux₄-p p v {x₃ = {!!}} (λ v₁ t₁ → cpsTerm e₂(λ v₂ t₂ →
--              CPSApp
--              (CPSApp (CPSApp (CPSVal v₁) (CPSVal v₂))
--               (CPSVal
--                (CPSFun
--                 (λ v₃ → CPSVal (CPSFun (λ t'' → κ₂ (CPSVar v₃) (CPSVar t'')))))))
--              (CPSVal t₂)) t₁) k t ⟩
--   cpsTerm (pcontext-plug p (Val (Var v)))
--     (λ v₁ t' →
--        cpsTerm e₂
--        (λ v₂ t₂ →
--           CPSApp
--           (CPSApp (CPSApp (CPSVal v₁) (CPSVal v₂))
--            (CPSVal
--             (CPSFun
--              (λ v₃ → CPSVal (CPSFun (λ t'' → κ₂ (CPSVar v₃) (CPSVar t'')))))))
--           (CPSVal t₂))
--        (CPSCons _ (CPSVar k) t'))
--     (CPSVar t)
--   ⟶⟨ {!!} ⟩
--   (cpsTerm (pcontext-plug p (Val (Var v)))
--        (λ v₁ →
--           cpsTerm e₂
--           (λ v₂ t₂ →
--              CPSApp
--              (CPSApp (CPSApp (CPSVal v₁) (CPSVal v₂))
--               (CPSVal
--                (CPSFun
--                 (λ v₃ →
--                    CPSVal
--                    (CPSFun
--                     (λ t'' → κ₂ (CPSVar v₃) (CPSCons x₃ (CPSVar k) (CPSVar t''))))))))
--              (CPSVal t₂)))
--        (CPSVar t))

--   ∎
-- aux₄-p (Frame (App₂ v₁) p) v {x₂}{x₃} κ k t = begin
--   (cpsTerm (pcontext-plug p (Val (Var v)))
--        (λ v₂ t₂ →
--           CPSApp
--           (CPSApp (CPSApp (CPSVal (cpsV v₁)) (CPSVal v₂))
--            (CPSVal
--             (CPSFun
--              (λ v₃ → CPSVal (CPSFun (λ t'' → κ (CPSVar v₃) (CPSVar t'')))))))
--           (CPSVal t₂))
--        (CPSCons (refl , refl , x₂) (CPSVar k) (CPSVar t)))

--   ⟶⟨ aux₄-p p v (λ v₂ t₂ →
--           CPSApp
--           (CPSApp (CPSApp (CPSVal (cpsV v₁)) (CPSVal v₂))
--            (CPSVal
--             (CPSFun
--              (λ v₃ → CPSVal (CPSFun (λ t'' → κ (CPSVar v₃) (CPSVar t'')))))))
--           (CPSVal t₂)) k t ⟩
--   cpsTerm (pcontext-plug p (Val (Var v)))
--     (λ v₂ t' →
--        CPSApp
--        (CPSApp (CPSApp (CPSVal (cpsV v₁)) (CPSVal v₂))
--         (CPSVal
--          (CPSFun
--           (λ v₃ → CPSVal (CPSFun (λ t'' → κ (CPSVar v₃) (CPSVar t'')))))))
--        (CPSVal (CPSCons {!!} (CPSVar k) t')))
--     (CPSVar t)
--   ⟶⟨ {!!} ⟩
--   (cpsTerm (pcontext-plug p (Val (Var v)))
--        (λ v₂ t₂ →
--           CPSApp
--           (CPSApp (CPSApp (CPSVal (cpsV v₁)) (CPSVal v₂))
--            (CPSVal
--             (CPSFun
--              (λ v₃ →
--                 CPSVal
--                 (CPSFun
--                  (λ t'' → κ (CPSVar v₃) (CPSCons x₃ (CPSVar k) (CPSVar t''))))))))
--           (CPSVal t₂))
--        (CPSVar t))

--   ∎
-- aux₄-p (Frame (Plus₁ e₂) p) v κ k t = {!!}
-- aux₄-p (Frame (Plus₂ v₁) p) v κ k t = {!!}


-- aux₄ : ∀ {var : cpstyp → Set}{μ₄ : trail}
--          {α} {x₄} {x₅} {α₁} {α₂}
--          {μ₀} {μ₃}
--          (e : term[ var ∘ cpsT ] x₄ ⟨ μ₃ ⟩ α₁ ⟨ x₅ ⇒ α₂ , μ₀ ⟩ α)
--          (κ : cpsvalue[ var ] (cpsT x₄) →  cpsvalue[ var ] (cpsM μ₃) →
--               cpsterm[ var ] (cpsT α₁))
--          (k : var (cpsT x₅ ⇛ (cpsM μ₄ ⇛ cpsT α₂)))
--          (t : var (cpsM (x₅ ⇒ α₂ , μ₀)))
--          (x₂ : compatible (x₅ ⇒ α₂ , μ₀) μ₀ μ₄)
--          (x₃ : compatible (x₅ ⇒ α₂ , μ₄) μ₃ μ₃) →

-- aux₄ : ∀ {var : cpstyp → Set}{τ}{α}{β}{μα}{μβ}{μk}
--          (e : term[ var ∘ cpsT ] τ ⟨ μα ⟩ α ⟨ μβ ⟩ β)
--          {c : compatible μk μβ μβ}
--          {c' : compatible μk μα μα}
--          (κ : cpsvalue[ var ] (cpsT τ) →  cpsvalue[ var ] (cpsM μα) →
--               cpsterm[ var ] (cpsT α))
--          (k : var (cpsM μk))
--          (t : var (cpsM μβ)) →
--        cpsreduce {var}
--        (cpsTerm e
--        (λ v t' →
--            κ v t')
--             (CPSCons c (CPSVar k) (CPSVar t)))
--        (cpsTerm e
--         (λ v t' →
--            κ v (CPSCons c' (CPSVar k) t'))
--         (CPSVar t))

-- aux₄ = {!!}


-- aux₄ : ∀ {var : cpstyp → Set}{τ}{α}{β}{μα}{μβ}{μk}
--          (e : term[ var ∘ cpsT ] τ ⟨ μα ⟩ α ⟨ μβ ⟩ β)
--          {c : compatible μk μβ μβ}
--          --{c' : compatible μk μα μα}
--          (κ : cpsvalue[ var ] (cpsT τ) →  cpsvalue[ var ] (cpsM μα) →
--               cpsterm[ var ] (cpsT α))
--          (k : var (cpsM μk))
--          (t : var (cpsM μβ)) →
--          Σ[ c' ∈ compatible μk μα μα ]
--          (cpsreduce {var}
--          (cpsTerm e
--          (λ v t' →
--              κ v t')
--               (CPSCons c (CPSVar k) (CPSVar t)))
--          (cpsTerm e
--           (λ v t' →
--              κ v (CPSCons c' (CPSVar k) t'))
--              (CPSVar t)))

-- aux₄ = {!!}
{-aux₄ (Val x) κ k t x₂ x₃ = {!!}
aux₄ {μ₄ = μ₄}{x₄ = x₄}{x₅ = x₅}{α₁ = α₁}{α₂ = α₂}{μ₃ = μ₃}(App {τ₂ = τ₂}{β = β}{μβ = μβ}{μγ = μγ} e e₁) κ k t x₂ x₃ = begin
  (cpsTerm e
       (λ v₁ →
          cpsTerm e₁
          (λ v₂ t₂ →
             CPSApp
             (CPSApp (CPSApp (CPSVal v₁) (CPSVal v₂))
              (CPSVal
               (CPSFun
                (λ v → CPSVal (CPSFun (λ t'' → κ (CPSVar v) (CPSVar t'')))))))
             (CPSVal t₂)))
       (CPSCons (refl , refl , x₂) (CPSVar k) (CPSVar t)))

  ⟶⟨ aux₄ {x₄ = τ₂ ⇒ x₄ ⟨ μ₃ ⟩ α₁ ⟨ μβ ⟩ β}{μ₃ = μγ} e
       (λ v₁ t₁ →
          cpsTerm e₁
          (λ v₂ t₂ →
             CPSApp
             (CPSApp (CPSApp (CPSVal v₁) (CPSVal v₂))
              (CPSVal
               (CPSFun
                (λ v → CPSVal (CPSFun (λ t'' → κ (CPSVar v) (CPSVar t'')))))))
             (CPSVal t₂))
          t₁)
       k t x₂ {!compatible-equal x₃ compatible (x₅ ⇒ α₂ , μ₄) μγ μγ!} ⟩
  cpsTerm e
    (λ v t' →
       cpsTerm e₁
       (λ v₂ t₂ →
          CPSApp
          (CPSApp (CPSApp (CPSVal v) (CPSVal v₂))
           (CPSVal
            (CPSFun
             (λ v₁ → CPSVal (CPSFun (λ t'' → κ (CPSVar v₁) (CPSVar t'')))))))
          (CPSVal t₂))
       (CPSCons _ (CPSVar k) t'))
    (CPSVar t)
  ⟶⟨ {!!} ⟩
  {!!}
  ⟶⟨ {!!} ⟩
  (cpsTerm e
       (λ v₁ →
          cpsTerm e₁
          (λ v₂ t₂ →
             CPSApp
             (CPSApp (CPSApp (CPSVal v₁) (CPSVal v₂))
              (CPSVal
               (CPSFun
                (λ v →
                   CPSVal
                   (CPSFun
                    (λ t'' →
                       κ (CPSVar v)
                       (CPSCons x₃ (CPSVar k) (CPSVar t''))))))))
             (CPSVal t₂)))
       (CPSVar t))

  ∎
aux₄ (Plus e e₁) κ k t x₂ x₃ = {!!}
aux₄ (Control x x₁ x₄ e) κ k t x₂ x₃ = {!!}
aux₄ (Prompt x e) κ k t x₂ x₃ = {!!}-}

-- aux₄ (Val x) κ k t x₂ x₃  = {!!}
-- aux₄ {μ₃ = x ⇒ x₁ , μ₃} (App e e₁) κ k t x₂ (refl , refl , x₃)  = ?
  -- (cpsTerm e
  --      (λ v₁ →
  --         cpsTerm e₁
  --         (λ v₂ t₂ →
  --            CPSApp
  --            (CPSApp (CPSApp (CPSVal v₁) (CPSVal v₂))
  --             (CPSVal
  --              (CPSFun
  --               (λ v → CPSVal (CPSFun (λ t'' → κ (CPSVar v) (CPSVar t'')))))))
  --            (CPSVal t₂)))
  --      (CPSCons (refl , refl , x₂) (CPSVar k) (CPSVar t)))

  -- ⟶⟨ aux₄ e 
  --         (λ v₁ t₁ → cpsTerm e₁
  --         (λ v₂ t₂ →
  --            CPSApp
  --            (CPSApp (CPSApp (CPSVal v₁) (CPSVal v₂))
  --             (CPSVal
  --              (CPSFun
  --               (λ v → CPSVal (CPSFun (λ t'' → κ (CPSVar v) (CPSVar t'')))))))
  --            (CPSVal t₂)) t₁ ) k t  ⟩
  -- cpsTerm e
  --   (λ v t' →
  --      cpsTerm e₁
  --      (λ v₂ t₂ →
  --         CPSApp
  --         (CPSApp (CPSApp (CPSVal v) (CPSVal v₂))
  --          (CPSVal
  --           (CPSFun
  --            (λ v₁ → CPSVal (CPSFun (λ t'' → κ (CPSVar v₁) (CPSVar t'')))))))
  --         (CPSVal t₂))
  --      (CPSCons {!!} (CPSVar k) t'))
  --   (CPSVar t)
  -- ⟶⟨ {!!} ⟩
  -- {!!}
  -- ⟶⟨ {!!} ⟩
  -- (cpsTerm e
  --      (λ v₁ →
  --         cpsTerm e₁
  --         (λ v₂ t₂ →
  --            CPSApp
  --            (CPSApp (CPSApp (CPSVal v₁) (CPSVal v₂))
  --             (CPSVal
  --              (CPSFun
  --               (λ v →
  --                  CPSVal
  --                  (CPSFun
  --                   (λ t'' → κ (CPSVar v) (CPSCons x₃ (CPSVar k) (CPSVar t''))))))))
  --            (CPSVal t₂)))
  --      (CPSVar t))

  -- ∎
  
-- aux₄ (Plus e e₁) κ k t x₂ x₃ = {!!}
-- aux₄ (Control x x₁ x₂ e) κ k t x₂ x₃ = {!!}
-- aux₄ (Prompt x e) κ k t x₂ x₃ = {!!}

{- aux₄ : ∀ {var : cpstyp → Set}{τ₄ τ₆ : typ}{μ₄ : trail}
         {α} {x₄} {x₅} {α₁} {α₂}
         {μ₀} {μ₃}
         (e : term[ var ∘ cpsT ] x₄ ⟨ μ₃ ⟩ α₁ ⟨ x₅ ⇒ α₂ , μ₀ ⟩ α)
         {x₂ : compatible (x₅ ⇒ α₂ , μ₀) μ₀ μ₄}
         {x₃ : compatible (x₅ ⇒ α₂ , μ₄) μ₃ μ₃}
         (κ : cpsvalue[ var ] (cpsT x₄ ⇛ (cpsM μ₃ ⇛ cpsT α₁)))
         (k : var (cpsT x₅ ⇛ (cpsM μ₄ ⇛ cpsT α₂)))
         (t : var (cpsM (x₅ ⇒ α₂ , μ₀))) →
       cpsreduce {var}
       (cpsTerm e
       (λ v t' →
           CPSApp (CPSApp (CPSVal κ) (CPSVal v)) (CPSVal t'))
            (CPSCons (refl , (refl , x₂)) (CPSVar k) (CPSVar t)))
       (cpsTerm e
        (λ v t' →
           CPSApp (CPSApp (CPSVal κ) (CPSVal v)) (CPSVal (CPSCons x₃ (CPSVar k) t')))
        (CPSVar t))

aux₄ (Val x) κ k t = {!!}
aux₄ (App e e₁) {x₂}{x₃} κ k t = begin
  (cpsTerm e
       (λ v₁ →
          cpsTerm e₁
          (λ v₂ t₂ →
             CPSApp
             (CPSApp (CPSApp (CPSVal v₁) (CPSVal v₂))
              (CPSVal
               (CPSFun
                (λ v →
                   CPSVal
                   (CPSFun
                    (λ t'' →
                       CPSApp (CPSApp (CPSVal κ) (CPSVal (CPSVar v)))
                       (CPSVal (CPSVar t''))))))))
             (CPSVal t₂)))
       (CPSCons (refl , refl , x₂) (CPSVar k) (CPSVar t)))

  ⟶⟨ {!aux₄ e ( cpsTerm e₁ (λ v₂ t₂ →
             CPSApp
             (CPSApp (CPSApp (CPSVal v₁) (CPSVal v₂))
              (CPSVal
               (CPSFun
                (λ v →
                   CPSVal
                   (CPSFun
                    (λ t'' →
                       CPSApp (CPSApp (CPSVal κ) (CPSVal (CPSVar v)))
                       (CPSVal (CPSVar t''))))))))
             (CPSVal t₂)) t₁)  k t!} ⟩
  {!!}
  ⟶⟨ {!!} ⟩
  (cpsTerm e
       (λ v₁ →
          cpsTerm e₁
          (λ v₂ t₂ →
             CPSApp
             (CPSApp (CPSApp (CPSVal v₁) (CPSVal v₂))
              (CPSVal
               (CPSFun
                (λ v →
                   CPSVal
                   (CPSFun
                    (λ t'' →
                       CPSApp (CPSApp (CPSVal κ) (CPSVal (CPSVar v)))
                       (CPSVal (CPSCons x₃ (CPSVar k) (CPSVar t'')))))))))
             (CPSVal t₂)))
       (CPSVar t))
       ∎
       
aux₄ (Plus e e₁) κ k t = {!!}
aux₄ (Control x x₁ x₂ e) κ k t = {!!}
aux₄ (Prompt x e) κ k t = {!!} -}
{--aux₄ (Val x) {x₂} {refl , refl , snd} κ k t 
     rewrite (compatible-equal x₂ snd) = r*Id
aux₄ (App e e₁) {x₂}{x₃} κ k t = begin
  (cpsTerm e
       (λ v₁ →
          cpsTerm e₁
          (λ v₂ t₂ →
             CPSApp
             (CPSApp (CPSApp (CPSVal v₁) (CPSVal v₂))
              (CPSVal
               (CPSFun
                (λ v →
                   CPSVal
                   (CPSFun
                    (λ t'' →
                       CPSApp (CPSApp (CPSVal (CPSVar κ)) (CPSVal (CPSVar v)))
                       (CPSVal (CPSVar t''))))))))
             (CPSVal t₂)))
       (CPSCons (refl , refl , x₂) (CPSVar k) (CPSVar t)))

  ⟶⟨ {!aux₄ e (λ v₁ → v₁) k t!} ⟩
  {!!}
  ⟶⟨ {!!} ⟩
  (cpsTerm e
       (λ v₁ →
          cpsTerm e₁
          (λ v₂ t₂ →
             CPSApp
             (CPSApp (CPSApp (CPSVal v₁) (CPSVal v₂))
              (CPSVal
               (CPSFun
                (λ v →
                   CPSVal
                   (CPSFun
                    (λ t'' →
                       CPSApp (CPSApp (CPSVal (CPSVar κ)) (CPSVal (CPSVar v)))
                       (CPSVal (CPSCons x₃ (CPSVar k) (CPSVar t'')))))))))
             (CPSVal t₂)))
       (CPSVar t))

  ∎


  
aux₄ (Plus e e₁) κ k t = {!!}
aux₄ (Control i c₁ c₂ e) {x₂}{x₃} κ k t = begin
  (CPSLet
       (CPSVal
        (CPSFun
         (λ v →
            CPSVal
            (CPSFun
             (λ k' →
                CPSVal
                (CPSFun
                 (λ t' →
                    CPSLet
                    (CPSVal
                     (CPSAppend c₂ (CPSCons (refl , refl , x₂) (CPSVar k) (CPSVar t))
                      (CPSCons c₁ (CPSVar k') (CPSVar t'))))
                    (λ t'' →
                       CPSApp (CPSApp (CPSVal (CPSVar κ)) (CPSVal (CPSVar v)))
                       (CPSVal (CPSVar t''))))))))))
       (λ x' → cpsTerm (e x') (CPSIdk i) CPSId))

  ⟶⟨ rLet₁ (rFun (λ x → rFun (λ x₁ → rFun (λ x₆ → rLetApp)))) ⟩
  CPSLet
    (CPSVal
     (CPSFun
      (λ z →
         CPSVal
         (CPSFun
          (λ z₁ →
             CPSVal
             (CPSFun
              (λ z₂ →
                 CPSApp
                 (CPSVal
                  (CPSFun
                   (λ t'' →
                      CPSApp (CPSApp (CPSVal (CPSVar κ)) (CPSVal (CPSVar z)))
                      (CPSVal (CPSVar t'')))))
                 (CPSVal
                  (CPSAppend c₂ (CPSCons (refl , refl , x₂) (CPSVar k) (CPSVar t))
                   (CPSCons c₁ (CPSVar z₁) (CPSVar z₂)))))))))))
    (λ x' → cpsTerm (e x') (CPSIdk i) CPSId)
  ⟶⟨ rLet₁ (rFun (λ x → rFun (λ x₁ → rFun (λ x₆ → rBeta (sApp Subst≠ (sVal sVar=)))))) ⟩
  CPSLet
    (CPSVal
     (CPSFun
      (λ z →
         CPSVal
         (CPSFun
          (λ z₁ →
             CPSVal
             (CPSFun
              (λ z₂ →
                 CPSApp (CPSApp (CPSVal (CPSVar κ)) (CPSVal (CPSVar z)))
                 (CPSVal
                  (CPSAppend c₂ (CPSCons (refl , refl , x₂) (CPSVar k) (CPSVar t))
                   (CPSCons c₁ (CPSVar z₁) (CPSVar z₂)))))))))))
    (λ x' → cpsTerm (e x') (CPSIdk i) CPSId)
  ⟶⟨ rLet₁ (rFun (λ x → rFun (λ x₁ → rFun (λ x₅ → rApp₂ rApdt)))) ⟩
  CPSLet
    (CPSVal
     (CPSFun
      (λ z →
         CPSVal
         (CPSFun
          (λ z₁ →
             CPSVal
             (CPSFun
              (λ z₂ →
                 CPSApp (CPSApp (CPSVal (CPSVar κ)) (CPSVal (CPSVar z)))
                 (CPSVal
                  (CPSCons c₂ (CPSCons (refl , refl , x₂) (CPSVar k) (CPSVar t))
                   (CPSCons c₁ (CPSVar z₁) (CPSVar z₂)))))))))))
    (λ x' → cpsTerm (e x') (CPSIdk i) CPSId)
  ⟶⟨ rLet₁ (rFun (λ x → rFun (λ x₁ → rFun (λ x₆ → rApp₂ (aux₄-con k t (CPSCons c₁ (CPSVar x₁) (CPSVar x₆))))))) ⟩
  CPSLet
    (CPSVal
     (CPSFun
      (λ z →
         CPSVal
         (CPSFun
          (λ z₁ →
             CPSVal
             (CPSFun
              (λ z₂ →
                 CPSApp (CPSApp (CPSVal (CPSVar κ)) (CPSVal (CPSVar z)))
                 (CPSVal
                  (CPSCons x₃ (CPSVar k)
                   (CPSCons c₂ (CPSVar t)
                    (CPSCons c₁ (CPSVar z₁) (CPSVar z₂))))))))))))
    (λ x' → cpsTerm (e x') (CPSIdk i) CPSId)
  ⟵⟨ rLet₁ (rFun (λ x → rFun (λ x₁ → rFun (λ x₆ → rApp₂ (rCon₂ rApdt))))) ⟩
  CPSLet
    (CPSVal
     (CPSFun
      (λ z →
         CPSVal
         (CPSFun
          (λ z₁ →
             CPSVal
             (CPSFun
              (λ z₂ →
                 CPSApp (CPSApp (CPSVal (CPSVar κ)) (CPSVal (CPSVar z)))
                 (CPSVal
                  (CPSCons x₃ (CPSVar k)
                   (CPSAppend c₂ (CPSVar t)
                    (CPSCons c₁ (CPSVar z₁) (CPSVar z₂))))))))))))
    (λ x' → cpsTerm (e x') (CPSIdk i) CPSId)
  ⟵⟨ rLet₁ (rFun (λ x → rFun (λ x₁ → rFun (λ x₆ → rBeta
      (sApp Subst≠ (sVal (sCon SubstV≠ sVar=))))))) ⟩
  CPSLet
    (CPSVal
     (CPSFun
      (λ z →
         CPSVal
         (CPSFun
          (λ z₁ →
             CPSVal
             (CPSFun
              (λ z₂ →
                 CPSApp
                 (CPSVal
                  (CPSFun
                   (λ t'' →
                      CPSApp (CPSApp (CPSVal (CPSVar κ)) (CPSVal (CPSVar z)))
                      (CPSVal (CPSCons x₃ (CPSVar k) (CPSVar t''))))))
                 (CPSVal
                  (CPSAppend c₂ (CPSVar t)
                   (CPSCons c₁ (CPSVar z₁) (CPSVar z₂)))))))))))
    (λ x' → cpsTerm (e x') (CPSIdk i) CPSId)
  ⟵⟨ rLet₁ (rFun (λ x → rFun (λ x₁ → rFun (λ x₆ → rLetApp)))) ⟩
  (CPSLet
       (CPSVal
        (CPSFun
         (λ v →
            CPSVal
            (CPSFun
             (λ k' →
                CPSVal
                (CPSFun
                 (λ t' →
                    CPSLet
                    (CPSVal
                     (CPSAppend c₂ (CPSVar t) (CPSCons c₁ (CPSVar k') (CPSVar t'))))
                    (λ t'' →
                       CPSApp (CPSApp (CPSVal (CPSVar κ)) (CPSVal (CPSVar v)))
                       (CPSVal (CPSCons x₃ (CPSVar k) (CPSVar t'')))))))))))
       (λ x' → cpsTerm (e x') (CPSIdk i) CPSId))

  ∎

{-
  
aux₄ (Prompt x e) {x₂} {refl , refl , snd} κ k t
     rewrite (compatible-equal x₂ snd) = r*Id -}

{- aux₄ : ∀ {var : cpstyp → Set}{τ₄ τ₆ : typ}{μ₄ : trail}
         {α} {x₄} {α₁}
         {μ₀} {μ₃}
         (e : term[ var ∘ cpsT ] x₄ ⟨ μ₃ ⟩ α₁ ⟨ x₄ ⇒ α₁ , μ₀ ⟩ α)
         {x₂ : compatible (x₄ ⇒ α₁ , μ₀) μ₀ μ₄}
         {x₃ : compatible (x₄ ⇒ α₁ , μ₄) μ₃ μ₃}
         (κ : var (cpsT x₄ ⇛ (cpsM μ₃ ⇛ cpsT α₁)))
         (k : var (cpsT x₄ ⇛ (cpsM μ₄ ⇛ cpsT α₁)))
         (t : var (cpsM (x₄ ⇒ α₁ , μ₀))) →
       cpsreduce {var}
       (cpsTerm e
       (λ v t' →
           CPSApp (CPSApp (CPSVal (CPSVar κ)) (CPSVal v)) (CPSVal t'))
            (CPSCons (refl , (refl , x₂)) (CPSVar k) (CPSVar t)))
       (cpsTerm e
        (λ v t' →
           CPSApp (CPSApp (CPSVal (CPSVar κ)) (CPSVal v)) (CPSVal (CPSCons x₃ (CPSVar k) t')))
        (CPSVar t))


aux₄ {μ₄ = μ₄}{α = α}{x₄ = x₄}{μ₀ = μ₀}(Val v) {x₂}{refl , refl , snd} κ k t
     rewrite (compatible-equal x₂ snd) = r*Id
aux₄ (App e e₁) {x₂}{x₃} κ k t = {!aux₄!}
aux₄ (Plus e e₁) κ k t = {!aux₄!}
aux₄  (Control i c₁ c₂ e) {x₂} {x₃} κ k t = begin
  (CPSLet
       (CPSVal
        (CPSFun
         (λ v →
            CPSVal
            (CPSFun
             (λ k' →
                CPSVal
                (CPSFun
                 (λ t' →
                    CPSLet
                    (CPSVal
                     (CPSAppend c₂ (CPSCons (refl , refl , x₂) (CPSVar k) (CPSVar t))
                      (CPSCons c₁ (CPSVar k') (CPSVar t'))))
                    (λ t'' →
                       CPSApp (CPSApp (CPSVal (CPSVar κ)) (CPSVal (CPSVar v)))
                       (CPSVal (CPSVar t''))))))))))
       (λ x' → cpsTerm (e x') (CPSIdk i) CPSId))

  ⟶⟨ rLet₁ (rFun (λ x → rFun (λ x₁ → rFun (λ x₅ → rLetApp)))) ⟩
  CPSLet
    (CPSVal
     (CPSFun
      (λ z →
         CPSVal
         (CPSFun
          (λ z₁ →
             CPSVal
             (CPSFun
              (λ z₂ →
                 CPSApp
                 (CPSVal
                  (CPSFun
                   (λ t'' →
                      CPSApp (CPSApp (CPSVal (CPSVar κ)) (CPSVal (CPSVar z)))
                      (CPSVal (CPSVar t'')))))
                 (CPSVal
                  (CPSAppend c₂ (CPSCons (refl , refl , x₂) (CPSVar k) (CPSVar t))
                   (CPSCons c₁ (CPSVar z₁) (CPSVar z₂)))))))))))
    (λ x' → cpsTerm (e x') (CPSIdk i) CPSId)
  ⟶⟨ rLet₁ (rFun (λ x → rFun (λ x₁ → rFun (λ x₅ → rBeta
      (sApp Subst≠ (sVal sVar=)))))) ⟩
  CPSLet
    (CPSVal
     (CPSFun
      (λ z →
         CPSVal
         (CPSFun
          (λ z₁ →
             CPSVal
             (CPSFun
              (λ z₂ →
                 CPSApp (CPSApp (CPSVal (CPSVar κ)) (CPSVal (CPSVar z)))
                 (CPSVal
                  (CPSAppend c₂ (CPSCons (refl , refl , x₂) (CPSVar k) (CPSVar t))
                   (CPSCons c₁ (CPSVar z₁) (CPSVar z₂)))))))))))
    (λ x' → cpsTerm (e x') (CPSIdk i) CPSId)
  ⟶⟨ rLet₁ (rFun (λ x → rFun (λ x₁ → rFun (λ x₅ → rApp₂ rApdt)))) ⟩
  CPSLet
    (CPSVal
     (CPSFun
      (λ z →
         CPSVal
         (CPSFun
          (λ z₁ →
             CPSVal
             (CPSFun
              (λ z₂ →
                 CPSApp (CPSApp (CPSVal (CPSVar κ)) (CPSVal (CPSVar z)))
                 (CPSVal
                  (CPSCons c₂ (CPSCons (refl , refl , x₂) (CPSVar k) (CPSVar t))
                   (CPSCons c₁ (CPSVar z₁) (CPSVar z₂)))))))))))
    (λ x' → cpsTerm (e x') (CPSIdk i) CPSId)
  ⟶⟨ {!!} ⟩
  {!!}
  ⟵⟨ rLet₁ (rFun (λ x → rFun (λ x₁ → rFun (λ x₅ → rApp₂ {!rConst!})))) ⟩
  CPSLet
    (CPSVal
     (CPSFun
      (λ z →
         CPSVal
         (CPSFun
          (λ z₁ →
             CPSVal
             (CPSFun
              (λ z₂ →
                 CPSApp (CPSApp (CPSVal (CPSVar κ)) (CPSVal (CPSVar z)))
                 (CPSVal
                  (CPSCons x₃ (CPSVar k)
                   (CPSAppend c₂ (CPSVar t)
                    (CPSCons c₁ (CPSVar z₁) (CPSVar z₂))))))))))))
    (λ x' → cpsTerm (e x') (CPSIdk i) CPSId)
  ⟵⟨ rLet₁ (rFun (λ x → rFun (λ x₁ → rFun (λ x₅ → rBeta
      (sApp Subst≠ (sVal (sCon SubstV≠ sVar=))))))) ⟩
  CPSLet
    (CPSVal
     (CPSFun
      (λ z →
         CPSVal
         (CPSFun
          (λ z₁ →
             CPSVal
             (CPSFun
              (λ z₂ →
                 CPSApp
                 (CPSVal
                  (CPSFun
                   (λ t'' →
                      CPSApp (CPSApp (CPSVal (CPSVar κ)) (CPSVal (CPSVar z)))
                      (CPSVal (CPSCons x₃ (CPSVar k) (CPSVar t''))))))
                 (CPSVal
                  (CPSAppend c₂ (CPSVar t)
                   (CPSCons c₁ (CPSVar z₁) (CPSVar z₂)))))))))))
    (λ x' → cpsTerm (e x') (CPSIdk i) CPSId)
  ⟵⟨ rLet₁ (rFun (λ x → rFun (λ x₁ → rFun (λ x₅ → rLetApp)))) ⟩
  (CPSLet
       (CPSVal
        (CPSFun
         (λ v →
            CPSVal
            (CPSFun
             (λ k' →
                CPSVal
                (CPSFun
                 (λ t' →
                    CPSLet
                    (CPSVal
                     (CPSAppend c₂ (CPSVar t) (CPSCons c₁ (CPSVar k') (CPSVar t'))))
                    (λ t'' →
                       CPSApp (CPSApp (CPSVal (CPSVar κ)) (CPSVal (CPSVar v)))
                       (CPSVal (CPSCons x₃ (CPSVar k) (CPSVar t'')))))))))))
       (λ x' → cpsTerm (e x') (CPSIdk i) CPSId))

  ∎
aux₄ (Prompt x e) κ k t = {!!} -}

{- aux₃ : ∀ {var}
         --{t : cpsvalue[ var ] cpsM μα}
         {α} {x₄} {α = α₁}
         -- {k
         --  : cpsvalue[ var ] cpsT τ₁ →
         --    cpsvalue[ var ] cpsM μα → cpsterm[ var ] cpsT α₁}
         -- {sch : schematicV k} {sch' : schematicV′ k}
         {μ₀} {μ₃}
         -- {p₁
         --  : pcontext[ var ∘ cpsT , τ ⟨ μα ⟩ α ⟨ μβ ⟩ τ₁ ] x₄ ⟨ μ₃ ⟩ α₁ ⟨ ∙ ⟩
         --    τ₁}
         -- (p₂
         --  : pcontext[ var ∘ cpsT , τ ⟨ μα' ⟩ α' ⟨ μα' ⟩ α' ] x₄ ⟨ μ₃ ⟩ α₁ ⟨
         --    x₄ ⇒ α₁ , μ₀ ⟩ α)
         (e : term[ var ∘ cpsT ] x₄ ⟨ μ₃ ⟩ α₁ ⟨ x₄ ⇒ α₁ , μ₀ ⟩ α)
         {x₀ : is-id-trail x₄ α₁ μ₃}
         --{x₁ : is-id-trail γ γ' μᵢ}
         {x₂ : compatible (x₄ ⇒ α₁ , μ₀) μ₀ μ₃}
         --{x₃ : compatible μβ (x₄ ⇒ α₁ , μ₀) μα}
         --{x : same-pcontext p₁ p₂}
         -- {e = e₁
         --  : (var ∘ cpsT) (τ ⇒ x₄ ⟨ μ₃ ⟩ α₁ ⟨ x₄ ⇒ α₁ , μ₀ ⟩ α) →
         --    term[ var ∘ cpsT ] γ ⟨ μᵢ ⟩ γ' ⟨ ∙ ⟩ τ₁}
         --(x₆ : var (cpsT τ))
         (k : var (cpsT x₄ ⇛ (cpsM μ₃ ⇛ cpsT α₁)))
         (t : var (cpsM (x₄ ⇒ α₁ , μ₀))) →
       cpsreduce {var}
       (cpsTerm e
       (λ v t' →
           CPSApp (CPSApp (CPSVal (CPSVar k)) (CPSVal v)) (CPSVal t'))
            (CPSCons (refl , (refl , x₂)) (CPSVar k) (CPSVar t)))
       (cpsTerm e
        (λ v t' →
           CPSApp (CPSApp (CPSVal (CPSVar k)) (CPSVal v)) (CPSVal (CPSCons {!x₂!} (CPSVar k) t')))
        (CPSVar t))

aux₃ = {!!}

-- aux₁ : ∀ {var}
--          --{t : cpsvalue[ var ] cpsM μα}
--          {α} {x₄} {α = α₁}
--          -- {k
--          --  : cpsvalue[ var ] cpsT τ₁ →
--          --    cpsvalue[ var ] cpsM μα → cpsterm[ var ] cpsT α₁}
--          -- {sch : schematicV k} {sch' : schematicV′ k}
--          {μ₀} {μ₃}
--          -- {p₁
--          --  : pcontext[ var ∘ cpsT , τ ⟨ μα ⟩ α ⟨ μβ ⟩ τ₁ ] x₄ ⟨ μ₃ ⟩ α₁ ⟨ ∙ ⟩
--          --    τ₁}
--          -- (p₂
--          --  : pcontext[ var ∘ cpsT , τ ⟨ μα' ⟩ α' ⟨ μα' ⟩ α' ] x₄ ⟨ μ₃ ⟩ α₁ ⟨
--          --    x₄ ⇒ α₁ , μ₀ ⟩ α)
--          (e : term[ var ∘ cpsT ] x₄ ⟨ μ₃ ⟩ α₁ ⟨ x₄ ⇒ α₁ , μ₀ ⟩ α)
--          {x₀ : is-id-trail x₄ α₁ μ₃}
--          --{x₁ : is-id-trail γ γ' μᵢ}
--          {x₂ : compatible (x₄ ⇒ α₁ , μ₀) μ₀ μ₃}
--          --{x₃ : compatible μβ (x₄ ⇒ α₁ , μ₀) μα}
--          --{x : same-pcontext p₁ p₂}
--          -- {e = e₁
--          --  : (var ∘ cpsT) (τ ⇒ x₄ ⟨ μ₃ ⟩ α₁ ⟨ x₄ ⇒ α₁ , μ₀ ⟩ α) →
--          --    term[ var ∘ cpsT ] γ ⟨ μᵢ ⟩ γ' ⟨ ∙ ⟩ τ₁}
--          --(x₆ : var (cpsT τ))
--          (k : var (cpsT x₄ ⇛ (cpsM μ₃ ⇛ cpsT α₁)))
--          (t : var (cpsM (x₄ ⇒ α₁ , μ₀))) →
--        cpsreduce {var}
--        (cpsTerm e (CPSIdk x₀)
--         (CPSFun
--          (λ v →
--             CPSVal
--             (CPSFun
--              (λ t' →
--                 CPSApp (CPSApp (CPSVal (CPSVar k)) (CPSVal (CPSVar v)))
--                 (CPSVal (CPSCons x₂ (CPSVar t) (CPSVar t'))))))))
--        (cpsTerm e
--         (λ v t'' →
--            CPSApp (CPSApp (CPSVal (CPSVar k)) (CPSVal v)) (CPSVal t''))
--         (CPSVar t))

-- aux₁ {α = α₁} {α = .α₁} (Val x) {x₀} {x₂} k t = {!!}
-- aux₁ {α = α₁} {α = α₂} (App e e₁) {x₀} {x₂} k t = {!!}
-- aux₁ {α = α₁} {α = α₂} (Plus e e₁) {x₀} {x₂} k t = {!!}
-- aux₁ {α = α₁} {α = α₂} (Control x x₁ x₃ e) {x₀} {x₂} k t = {!!}
-- aux₁ {α = α₁} {α = .α₁} (Prompt x e) {x₀} {x₂} k t = {!!}

-- aux-p : ∀ {var} {α}
--          -- {k
--          --  : cpsvalue[ var ] cpsT τ₁ →
--          --    cpsvalue[ var ] cpsM μα → cpsterm[ var ] cpsT α}
--          -- {t : cpsvalue[ var ] cpsM μα} {sch : schematicV k}
--          -- {sch' : schematicV′ k}
--          {α₁} {τ₂} {τ} {μα'} {α'}
--          {x₄} {x₅} {μ₀} {μ₃}
--          -- {p₁
--          --  : pcontext[ var ∘ cpsT , τ ⟨ μα ⟩ α₁ ⟨ μβ ⟩ τ₁ ] τ₂ ⟨ μ₃ ⟩ α ⟨ ∙ ⟩
--          --    τ₁}
--          (p₂
--           : pcontext[ var ∘ cpsT , τ ⟨ μα' ⟩ α' ⟨ μα' ⟩ α' ] τ₂ ⟨ μ₃ ⟩ α ⟨
--             x₄ ⇒ x₅ , μ₀ ⟩ α₁)
--          --(e : term[ var ∘ cpsT ] τ₂ ⟨ μ₃ ⟩ α ⟨ x₄ ⇒ x₅ , μ₀ ⟩ α₁)
--          {x₀ : is-id-trail τ₂ α μ₃}
--          --{x₁ : is-id-trail γ γ' μᵢ}
--          {x₂ : compatible (τ₂ ⇒ α , μ₃) (x₄ ⇒ x₅ , μ₀) (x₄ ⇒ x₅ , μ₀)}
--          --{x₃ : compatible μβ (x₄ ⇒ x₅ , μ₀) μα} {x : same-pcontext p₁ p₂}
--          -- {e = e₁
--          --  : (var ∘ cpsT) (τ ⇒ τ₂ ⟨ μ₃ ⟩ α ⟨ x₄ ⇒ x₅ , μ₀ ⟩ α₁) →
--          --    term[ var ∘ cpsT ] γ ⟨ μᵢ ⟩ γ' ⟨ ∙ ⟩ τ₁}
--          (x₆ : var (cpsT τ))
--          (k : var (cpsT τ₂ ⇛ (cpsM μ₃ ⇛ cpsT α)))
--          (t : var (cpsM (x₄ ⇒ x₅ , μ₀))) →
--        cpsreduce {var}
--        (cpsTerm (pcontext-plug p₂ (Val (Var x₆))) (CPSIdk x₀)
--         (CPSCons x₂ (CPSVar k) (CPSVar t)))
--        (cpsTerm (pcontext-plug p₂ (Val (Var x₆)))
--         (λ v t'' →
--            CPSApp (CPSApp (CPSVal (CPSVar k)) (CPSVal v)) (CPSVal t''))
--         (CPSVar t))

-- aux-p Hole x₆ k t = {!!}
-- aux-p (Frame (App₁ e₁) p₂) {x₀}{x₂} x₆ k t = begin
--   (cpsTerm (pcontext-plug p₂ (Val (Var x₆)))
--        (λ v₁ →
--           cpsTerm e₁
--           (λ v₂ t₂ →
--              CPSApp
--              (CPSApp (CPSApp (CPSVal v₁) (CPSVal v₂))
--               (CPSVal
--                (CPSFun
--                 (λ v →
--                    CPSVal (CPSFun (λ t'' → CPSIdk x₀ (CPSVar v) (CPSVar t'')))))))
--              (CPSVal t₂)))
--        (CPSCons x₂ (CPSVar k) (CPSVar t)))
--   ⟶⟨ {!!} ⟩
--   {!!}
--   ⟶⟨ {!!} ⟩
--   (cpsTerm (pcontext-plug p₂ (Val (Var x₆)))
--        (λ v₁ →
--           cpsTerm e₁
--           (λ v₂ t₂ →
--              CPSApp
--              (CPSApp (CPSApp (CPSVal v₁) (CPSVal v₂))
--               (CPSVal
--                (CPSFun
--                 (λ v →
--                    CPSVal
--                    (CPSFun
--                     (λ t'' →
--                        CPSApp (CPSApp (CPSVal (CPSVar k)) (CPSVal (CPSVar v)))
--                        (CPSVal (CPSVar t''))))))))
--              (CPSVal t₂)))
--        (CPSVar t))

--   ∎
-- aux-p (Frame (App₂ v₁) p₂) x₆ k t = {!!}
-- aux-p (Frame (Plus₁ e₂) p₂) x₆ k t = {!!}
-- aux-p (Frame (Plus₂ v₁) p₂) x₆ k t = {!!}

-- aux : ∀ {var} {α}
--          -- {k
--          --  : cpsvalue[ var ] cpsT τ₁ →
--          --    cpsvalue[ var ] cpsM μα → cpsterm[ var ] cpsT α}
--          -- {t : cpsvalue[ var ] cpsM μα} {sch : schematicV k}
--          -- {sch' : schematicV′ k}
--          {α₁} {τ₂}
--          {x₄} {x₅} {μ₀} {μ₃}
--          -- {p₁
--          --  : pcontext[ var ∘ cpsT , τ ⟨ μα ⟩ α₁ ⟨ μβ ⟩ τ₁ ] τ₂ ⟨ μ₃ ⟩ α ⟨ ∙ ⟩
--          --    τ₁}
--          -- (p₂
--          --  : pcontext[ var ∘ cpsT , τ ⟨ μα' ⟩ α' ⟨ μα' ⟩ α' ] τ₂ ⟨ μ₃ ⟩ α ⟨
--          --    x₄ ⇒ x₅ , μ₀ ⟩ α₁)
--          (e : term[ var ∘ cpsT ] τ₂ ⟨ μ₃ ⟩ α ⟨ x₄ ⇒ x₅ , μ₀ ⟩ α₁)
--          {x₀ : is-id-trail τ₂ α μ₃}
--          --{x₁ : is-id-trail γ γ' μᵢ}
--          {x₂ : compatible (τ₂ ⇒ α , μ₃) (x₄ ⇒ x₅ , μ₀) (x₄ ⇒ x₅ , μ₀)}
--          --{x₃ : compatible μβ (x₄ ⇒ x₅ , μ₀) μα} {x : same-pcontext p₁ p₂}
--          -- {e = e₁
--          --  : (var ∘ cpsT) (τ ⇒ τ₂ ⟨ μ₃ ⟩ α ⟨ x₄ ⇒ x₅ , μ₀ ⟩ α₁) →
--          --    term[ var ∘ cpsT ] γ ⟨ μᵢ ⟩ γ' ⟨ ∙ ⟩ τ₁}
--          --(x₆ : var (cpsT τ))
--          (k : var (cpsT τ₂ ⇛ (cpsM μ₃ ⇛ cpsT α)))
--          (t : var (cpsM (x₄ ⇒ x₅ , μ₀))) →
--        cpsreduce {var}
--        (cpsTerm e (CPSIdk x₀)
--         (CPSCons x₂ (CPSVar k) (CPSVar t)))
--        (cpsTerm e
--         (λ v t'' →
--            CPSApp (CPSApp (CPSVal (CPSVar k)) (CPSVal v)) (CPSVal t''))
--         (CPSVar t))
-- aux (Val x) {refl , refl , refl} {refl , refl , snd} k t = begin
--   (CPSIdk (refl , refl , refl) (cpsV x)
--        (CPSCons (refl , refl , snd) (CPSVar k) (CPSVar t)))

--   ⟶⟨ rIdkt ⟩
--   CPSApp
--     (CPSApp
--      (CPSVal (CPSCons (refl , refl , snd) (CPSVar k) (CPSVar t)))
--      (CPSVal (cpsV x)))
--     (CPSVal CPSId)
--   ⟶⟨ rApp₁ (rApp₁ rConst) ⟩
--   CPSApp
--     (CPSApp
--      (CPSVal
--       (CPSFun
--        (λ v →
--           CPSVal
--           (CPSFun
--            (λ t' →
--               CPSApp (CPSApp (CPSVal (CPSVar k)) (CPSVal (CPSVar v)))
--               (CPSVal (CPSCons refl (CPSVar t) (CPSVar t'))))))))
--      (CPSVal (cpsV x)))
--     (CPSVal CPSId)
--   ⟶⟨ rApp₁ (rBeta (sVal (sFun (λ x₁ → sApp (sApp Subst≠ (sVal sVar=)) Subst≠)))) ⟩
--   CPSApp
--     (CPSVal
--      (CPSFun
--       (λ z →
--          CPSApp (CPSApp (CPSVal (CPSVar k)) (CPSVal (cpsV x)))
--          (CPSVal (CPSCons refl (CPSVar t) (CPSVar z))))))
--     (CPSVal CPSId)
--   ⟶⟨ rBeta (sApp Subst≠ (sVal (sCon SubstV≠ sVar=))) ⟩
--   CPSApp (CPSApp (CPSVal (CPSVar k)) (CPSVal (cpsV x)))
--     (CPSVal (CPSCons refl (CPSVar t) CPSId))
--   ⟶⟨ rApp₂ rConsid ⟩
--   CPSApp (CPSApp (CPSVal (CPSVar k)) (CPSVal (cpsV x)))
--     (CPSVal (CPSVar t))

--   ∎
-- aux (App e e₁) {x₀} {refl , refl , snd} k t = begin
--   (cpsTerm e
--        (λ v₁ →
--           cpsTerm e₁
--           (λ v₂ t₂ →
--              CPSApp
--              (CPSApp (CPSApp (CPSVal v₁) (CPSVal v₂))
--               (CPSVal
--                (CPSFun
--                 (λ v →
--                    CPSVal (CPSFun (λ t'' → CPSIdk x₀ (CPSVar v) (CPSVar t'')))))))
--              (CPSVal t₂)))
--        (CPSCons (refl , refl , snd) (CPSVar k) (CPSVar t)))

--   ⟶⟨ {!!} ⟩
--   {!!}
--   ⟶⟨ {!aux!} ⟩
--   (cpsTerm e
--        (λ v₁ →
--           cpsTerm e₁
--           (λ v₂ t₂ →
--              CPSApp
--              (CPSApp (CPSApp (CPSVal v₁) (CPSVal v₂))
--               (CPSVal
--                (CPSFun
--                 (λ v →
--                    CPSVal
--                    (CPSFun
--                     (λ t'' →
--                        CPSApp (CPSApp (CPSVal (CPSVar k)) (CPSVal (CPSVar v)))
--                        (CPSVal (CPSVar t''))))))))
--              (CPSVal t₂)))
--        (CPSVar t))

--   ∎
-- aux (Plus e e₁) {x₀} {refl , snd} k t = {!!}

-- aux (Control x x₁ x₂ e) {x₀} {refl , refl , snd} k t = begin
--   (CPSLet
--        (CPSVal
--         (CPSFun
--          (λ v →
--             CPSVal
--             (CPSFun
--              (λ k' →
--                 CPSVal
--                 (CPSFun
--                  (λ t' →
--                     CPSLet
--                     (CPSVal
--                      (CPSAppend x₂ (CPSCons (refl , refl , snd) (CPSVar k) (CPSVar t))
--                       (CPSCons x₁ (CPSVar k') (CPSVar t'))))
--                     (λ t'' → CPSIdk x₀ (CPSVar v) (CPSVar t'')))))))))
--        (λ x' → cpsTerm (e x') (CPSIdk x) CPSId))

--   ⟶⟨ rLet₁ (rFun (λ x₃ → rFun (λ x₄ → rFun (λ x₅ → rLet₁ (rAppend₁ rConst))))) ⟩
--   CPSLet
--     (CPSVal
--      (CPSFun
--       (λ z →
--          CPSVal
--          (CPSFun
--           (λ z₁ →
--              CPSVal
--              (CPSFun
--               (λ z₂ →
--                  CPSLet
--                  (CPSVal
--                   (CPSAppend x₂
--                    (CPSFun
--                     (λ v →
--                        CPSVal
--                        (CPSFun
--                         (λ t' →
--                            CPSApp (CPSApp (CPSVal (CPSVar k)) (CPSVal (CPSVar v)))
--                            (CPSVal (CPSCons snd (CPSVar t) (CPSVar t')))))))
--                    (CPSCons x₁ (CPSVar z₁) (CPSVar z₂))))
--                  (λ t'' → CPSIdk x₀ (CPSVar z) (CPSVar t'')))))))))
--     (λ x' → cpsTerm (e x') (CPSIdk x) CPSId)
--   ⟶⟨ rLet₁ (rFun (λ x₃ → rFun (λ x₄ → rFun (λ x₅ → {!!})))) ⟩
--   {!!}
--   ⟶⟨ {!!} ⟩
--   (CPSLet
--        (CPSVal
--         (CPSFun
--          (λ v →
--             CPSVal
--             (CPSFun
--              (λ k' →
--                 CPSVal
--                 (CPSFun
--                  (λ t' →
--                     CPSLet
--                     (CPSVal
--                      (CPSAppend x₂ (CPSVar t) (CPSCons x₁ (CPSVar k') (CPSVar t'))))
--                     (λ t'' →
--                        CPSApp (CPSApp (CPSVal (CPSVar k)) (CPSVal (CPSVar v)))
--                        (CPSVal (CPSVar t''))))))))))
--        (λ x' → cpsTerm (e x') (CPSIdk x) CPSId))

--   ∎
  
-- aux (Prompt x e) {refl , refl , refl} {refl , refl , snd} k t = begin
--   (CPSLet (cpsTerm e (CPSIdk x) CPSId)
--        (λ v →
--           CPSIdk (refl , refl , refl) (CPSVar v)
--           (CPSCons (refl , refl , snd) (CPSVar k) (CPSVar t))))

--   ⟶⟨ rLet₂ (λ x₁ → rIdkt) ⟩
--   CPSLet (cpsTerm e (CPSIdk x) CPSId)
--     (λ z →
--        CPSApp
--        (CPSApp
--         (CPSVal (CPSCons (refl , refl , snd) (CPSVar k) (CPSVar t)))
--         (CPSVal (CPSVar z)))
--        (CPSVal CPSId))
--   ⟶⟨ rLet₂ (λ x₁ → rApp₁ (rApp₁ rConst)) ⟩
--   CPSLet (cpsTerm e (CPSIdk x) CPSId)
--     (λ z →
--        CPSApp
--        (CPSApp
--         (CPSVal
--          (CPSFun
--           (λ v →
--              CPSVal
--              (CPSFun
--               (λ t' →
--                  CPSApp (CPSApp (CPSVal (CPSVar k)) (CPSVal (CPSVar v)))
--                  (CPSVal (CPSCons refl (CPSVar t) (CPSVar t'))))))))
--         (CPSVal (CPSVar z)))
--        (CPSVal CPSId))
--   ⟶⟨ rLet₂ (λ x₁ → rApp₁ (rBeta (sVal (sFun (λ x₂ → sApp (sApp Subst≠ (sVal sVar=)) Subst≠))))) ⟩
--   CPSLet (cpsTerm e (CPSIdk x) CPSId)
--     (λ z →
--        CPSApp
--        (CPSVal
--         (CPSFun
--          (λ z₁ →
--             CPSApp (CPSApp (CPSVal (CPSVar k)) (CPSVal (CPSVar z)))
--             (CPSVal (CPSCons refl (CPSVar t) (CPSVar z₁))))))
--        (CPSVal CPSId))
--   ⟶⟨ rLet₂ (λ x₁ → rBeta (sApp Subst≠ (sVal (sCon SubstV≠ sVar=)))) ⟩
--   CPSLet (cpsTerm e (CPSIdk x) CPSId)
--     (λ z →
--        CPSApp (CPSApp (CPSVal (CPSVar k)) (CPSVal (CPSVar z)))
--        (CPSVal (CPSCons refl (CPSVar t) CPSId)))
--   ⟶⟨ rLet₂ (λ x₁ → rApp₂ rConsid) ⟩
--   (CPSLet (cpsTerm e (CPSIdk x) CPSId)
--        (λ v →
--           CPSApp (CPSApp (CPSVal (CPSVar k)) (CPSVal (CPSVar v)))
--           (CPSVal (CPSVar t))))

--   ∎ -}


-}


correctEta : {var : cpstyp → Set} {τ₁ α β : typ} {μα μβ : trail}
             {μs : trails[ μβ ] μα} →
             {e e′ : term[ var ∘ cpsT ] τ₁ ⟨ μs ⟩ α ⟨ μβ ⟩ β} →
             (k : cpsvalue[ var ] (cpsT τ₁) → cpsvalue[ var ] (cpsMs μs)
             → cpsterm[ var ] (cpsT α)) →
             (t : cpsvalue[ var ] (cpsM μβ)) →
             schematicV k →
             schematicV′ k →
             Reduce e e′ →
             cpsreduce (cpsTerm e k t) (cpsTerm e′ k t)  

correctEta {e′ = e′} k t sch sch'  (RBeta {e₁ = e₁} {v₂ = v₂} x) = begin
  cpsTerm (App (Val (Fun e₁)) (Val v₂)) k t
  ⟶⟨ rApp₁ (rApp₁ (rBeta (sVal (sFun (λ x₁ → sVal (sFun (λ x₂ → eSubst  x λ x₃ → sApp (sApp Subst≠ (sVal x₃)) Subst≠))))))) ⟩
  CPSApp
    (CPSApp
     (CPSVal
      (CPSFun
       (λ z →
          CPSVal
          (CPSFun
           (λ z₁ →
              cpsTerm e′
              (λ v t''' →
                 CPSApp (CPSApp (CPSVal (CPSVar z)) (CPSVal v)) (CPSVal t'''))
              (CPSVar z₁))))))
     (CPSVal
      (CPSFun
       (λ v → CPSVal (CPSFun (λ t'' → k (CPSVar v) (CPSVar t'')))))))
    (CPSVal t)
  ⟶⟨ rApp₁ (rBeta (sVal (sFun (λ x₁ → kSubst e′
                                          (λ y →
                                             λ v t''' → CPSApp (CPSApp (CPSVal y) (CPSVal v)) (CPSVal t'''))
                                          (λ x₂ t₁ → sApp (sApp (sVal sVar=) Subst≠)
                                          Subst≠))))) ⟩
  CPSApp
    (CPSVal
     (CPSFun
      (λ z →
         cpsTerm e′
         (λ z₁ z₂ →
            CPSApp
            (CPSApp
             (CPSVal
              (CPSFun
               (λ v → CPSVal (CPSFun (λ t'' → k (CPSVar v) (CPSVar t''))))))
             (CPSVal z₁))
            (CPSVal z₂))
         (CPSVar z))))
    (CPSVal t)
  ⟶⟨ rBeta (tSubst e′ λ t₁ v₃ → sApp Subst≠ (sVal sVar=)) ⟩
  cpsTerm e′
    (λ z₁ z₂ →
       CPSApp
       (CPSApp
        (CPSVal
         (CPSFun
          (λ v → CPSVal (CPSFun (λ t'' → k (CPSVar v) (CPSVar t''))))))
        (CPSVal z₁))
       (CPSVal z₂))
    t
    ⟶⟨ correctCont e′
         (λ z₁ z₂ →
            CPSApp
            (CPSApp
             (CPSVal
              (CPSFun
               (λ v → CPSVal (CPSFun (λ t'' → k (CPSVar v) (CPSVar t''))))))
             (CPSVal z₁))
            (CPSVal z₂))
            {k}
         (λ v t₁ → sApp (sApp Subst≠ (sVal sVar=)) Subst≠)
         (λ v t₁ → (begin
           (CPSApp
       (CPSApp
        (CPSVal
         (CPSFun
          (λ v₁ → CPSVal (CPSFun (λ t'' → k (CPSVar v₁) (CPSVar t''))))))
        (CPSVal (cpsV v)))
       (CPSVal t₁))
        ⟶⟨ rApp₁ (rBeta (sVal (sFun (λ x₁ → sch v (CPSVar x₁))))) ⟩
        CPSApp (CPSVal (CPSFun (λ z → k (cpsV v) (CPSVar z)))) (CPSVal t₁)
        ⟶⟨ rBeta (sch' t₁ (cpsV v)) ⟩
        (k (cpsV v) t₁)
        ∎)) ⟩
  cpsTerm e′ k t
  ∎ 


  
correctEta k t sch sch' (RPlus {τ₂} {μα} {n₁} {n₂}) = begin
  (CPSLet (CPSPlus (CPSVal (CPSNum n₁)) (CPSVal (CPSNum n₂))) (λ v → k (CPSVar v) t))
  ⟶⟨ rLet₁ rPlus ⟩
  CPSLet (CPSVal (CPSNum (n₁ + n₂))) (λ v → k (CPSVar v) t)
  ⟶⟨ rLet (sch (Num (n₁ + n₂)) t) ⟩
  k (CPSNum (n₁ + n₂)) t
  ∎
 
correctEta k t sch sch' (RFrame  (App₁ e₃) x) = correctEta (λ v₁ →
                                                      cpsTerm e₃
                                                      (λ v₂ t₂ →
                                                         CPSApp
                                                         (CPSApp (CPSApp (CPSVal v₁) (CPSVal v₂))
                                                          (CPSVal
                                                           (CPSFun
                                                            (λ v → CPSVal (CPSFun (λ t'' → k (CPSVar v) (CPSVar t'')))))))
                                                         (CPSVal t₂))) t (λ v t₁ →
                                                         kSubst e₃
                                                           (λ x₁ →
                                                              λ v₂ t₂ →
                                                                CPSApp
                                                                (CPSApp (CPSApp (CPSVal x₁) (CPSVal v₂))
                                                                 (CPSVal
                                                                  (CPSFun
                                                                   (λ v₁ → CPSVal (CPSFun (λ t'' → k (CPSVar v₁) (CPSVar t'')))))))
                                                                (CPSVal t₂))
                                                           (λ x₁ t₂ → sApp (sApp (sApp (sVal sVar=) Subst≠)
                                                           Subst≠) Subst≠)) (λ t₁ v₂ → tSubst e₃ λ t₂ v₃ →
                                                           sApp (sApp Subst≠ Subst≠) (sVal sVar=)) x
                                                           
correctEta k t sch sch' (RFrame (App₂ v₁) x) = correctEta (λ v₂ t₂ →
                                                     CPSApp
                                                     (CPSApp (CPSApp (CPSVal (cpsV v₁)) (CPSVal v₂))
                                                      (CPSVal
                                                       (CPSFun
                                                        (λ v → CPSVal (CPSFun (λ t'' → k (CPSVar v) (CPSVar t'')))))))
                                                     (CPSVal t₂)) t
                                                     (λ v t₁ → sApp (sApp (sApp Subst≠ (sVal sVar=))
                                                     Subst≠) Subst≠)
                                                     (λ t₁ v₂ → sApp Subst≠ (sVal sVar=))  x
                                                     
correctEta k t sch sch'  (RFrame (Plus₁ e₃) x) = correctEta (λ v₁ →  cpsTerm e₃
                                                                          (λ v₂ t₂ →
                                                                             CPSLet (CPSPlus (CPSVal v₁) (CPSVal v₂))
                                                                             (λ v → k (CPSVar v) t₂))) t
                                                                             (λ v t₁ →
                                                                             kSubst e₃
                                                                               (λ x₁ →
                                                                                  λ v₂ t₂ →
                                                                                    CPSLet (CPSPlus (CPSVal x₁) (CPSVal v₂)) (λ v₁ → k (CPSVar v₁) t₂))
                                                                               (λ x₁ t₂ → sLet (λ x₂ → Subst≠)
                                                                               (λ x₂ → sPlu (sVal sVar=) Subst≠)) )
                                                                                (λ t₁ v₂ → tSubst e₃ λ t₂ v₃ →
                                                                                sLet (λ x₁ → sch' t₂ (CPSVar x₁)) (λ x₁ → Subst≠))  x
                                                  
correctEta k t sch sch'  (RFrame (Plus₂ v₁) x) = correctEta (λ v₂ t₂ →
                                                      CPSLet (CPSPlus (CPSVal (cpsV v₁)) (CPSVal v₂))
                                                      (λ v → k (CPSVar v) t₂)) t (λ v t₁ → sLet (λ x₁ → Subst≠)
                                                      (λ x₁ → sPlu Subst≠ (sVal sVar=)))
                                                      (λ t₁ v₂ → sLet (λ x₁ → sch' t₁ (CPSVar x₁))
                                                      λ x₁ → Subst≠)  x
                                                      
correctEta k t sch sch' (RFrame {e₁ = e₁} {e₂ = e₂} (Pro x₁) x) = begin
  (CPSLet (cpsTerm e₁ (CPSIdk x₁) (CPSId))
       (λ v → k (CPSVar v) t))
  ⟶⟨ rLet₁ (correctEta (CPSIdk x₁) (CPSId) (λ v t₁ → sIdk sVar= SubstV≠) (λ t₁ v₂ → sIdk SubstV≠ sVar=) x) ⟩
  (CPSLet (cpsTerm e₂ (CPSIdk x₁) (CPSId))
       (λ v → k (CPSVar v) t))
  ∎
  
correctEta k t sch sch' (RPrompt {v₁ = v₁}) = begin
  (CPSLet (CPSIdk refl (cpsV v₁) (CPSId))
       (λ v → k (CPSVar v) t))
  ⟶⟨ rLet₁ rIdkid ⟩
  CPSLet (CPSVal (cpsV v₁)) (λ v → k (CPSVar v) t)
  ⟶⟨ rLetApp ⟩
  CPSApp (CPSVal (CPSFun (λ v → k (CPSVar v) t))) (CPSVal (cpsV v₁))
  ⟶⟨ rBeta (sch v₁ t) ⟩
  (k (cpsV v₁) t)
  ∎


{--correctEta {var} {τ₁} {α} {.α} {μα} {.μα} {.(Prompt x₀ (pcontext-plug p₁ (Control x₁ x₂ x₃ e₁)))} {.(Prompt x₁ (App (Val (Fun e₁)) (Val (Fun (λ x₆ → pcontext-plug p₂ (Val (Var x₆)))))))} k t sch sch' (RControl {τ = τ} {α' = α'} {β = τ₁} {β' = β'} {γ = γ} {γ' = γ'} {t₁ = t₁} {t₂ = t₂} {τ₂ = α} {τ₃ = τ₃} {τ₄ = τ₄} {τ₅ = τ₅} {μ₀ = x₄ ⇒ x₅ , μ₀} {μ₁ = μ₁} {μᵢ = μᵢ} {μα' = μα'} {μβ = μβ} {μβ' = μβ'} {μ₂ = μ₂} {μ₃ = ∙} {μ₄ = μ₄} {μ₅ = μ₅} p₁ p₂ {x₀} x₁ x₂ x₃ x e₁) = begin
  (CPSLet
       (cpsTerm (pcontext-plug p₁ (Control x₁ x₂ x₃ e₁)) (CPSIdk x₀)
        CPSId)
       (λ v → k (CPSVar v) t))

  ⟶⟨ rLet₁ (control-lemma p₁ p₂ x₁ x₂ x₃ x e₁ (CPSIdk x₀) CPSId (λ v t₃ → sIdk sVar= SubstV≠) (λ t₃ v₂ → sIdk SubstV≠ sVar=)) ⟩
  CPSLet
    (cpsTerm
     (App (Val (Fun (λ x₆ → pcontext-plug p₂ (Val (Var x₆)))))
      (Control x₁ x₂ refl e₁))
     (CPSIdk x₀) CPSId)
    (λ v → k (CPSVar v) t)
  ⟶⟨ rLet₁ (rLet₁ (rFun (λ x₆ → rFun (λ x₇ → rFun (λ x₈ → rLet₂ (λ x₉ →
      rApp₁ (rApp₁ (rBeta (sVal (sFun (λ x₁₀ → sVal (sFun (λ x₁₁ →
      eSubst (subst-context p₂ (Var x₆)) (λ x₁₂ → sApp (sApp Subst≠ (sVal x₁₂)) Subst≠)))))))))))))) ⟩
  CPSLet
    (CPSLet
     (CPSVal
      (CPSFun
       (λ z →
          CPSVal
          (CPSFun
           (λ z₁ →
              CPSVal
              (CPSFun
               (λ z₂ →
                  CPSLet
                  (CPSVal
                   (CPSAppend refl CPSId (CPSCons x₂ (CPSVar z₁) (CPSVar z₂))))
                  (λ z₃ →
                     CPSApp
                     (CPSApp
                      (CPSVal
                       (CPSFun
                        (λ z₄ →
                           CPSVal
                           (CPSFun
                            (λ z₅ →
                               cpsTerm (pcontext-plug p₂ (Val (Var z)))
                               (λ v t'' →
                                  CPSApp (CPSApp (CPSVal (CPSVar z₄)) (CPSVal v)) (CPSVal t''))
                               (CPSVar z₅))))))
                      (CPSVal
                       (CPSFun
                        (λ v →
                           CPSVal (CPSFun (λ t'' → CPSIdk x₀ (CPSVar v) (CPSVar t'')))))))
                     (CPSVal (CPSVar z₃))))))))))
     (λ x' → cpsTerm (e₁ x') (CPSIdk x₁) CPSId))
    (λ v → k (CPSVar v) t)
  ⟶⟨ rLet₁ (rLet₁ (rFun (λ x₆ → rFun (λ x₇ → rFun (λ x₈ → rLet₂ (λ x₉ →
      rApp₁ (rBeta (sVal (sFun (λ x₁₀ →
      kSubst (pcontext-plug p₂ (Val (Var x₆)))
        (λ y →
           λ v t'' → CPSApp (CPSApp (CPSVal y) (CPSVal v)) (CPSVal t''))
        (λ x₁₁ t₃ → sApp (sApp (sVal sVar=) Subst≠) Subst≠))))))))))) ⟩
  CPSLet
    (CPSLet
     (CPSVal
      (CPSFun
       (λ z →
          CPSVal
          (CPSFun
           (λ z₁ →
              CPSVal
              (CPSFun
               (λ z₂ →
                  CPSLet
                  (CPSVal
                   (CPSAppend refl CPSId (CPSCons x₂ (CPSVar z₁) (CPSVar z₂))))
                  (λ z₃ →
                     CPSApp
                     (CPSVal
                      (CPSFun
                       (λ z₄ →
                          cpsTerm (pcontext-plug p₂ (Val (Var z)))
                          (λ v t'' →
                             CPSApp
                             (CPSApp
                              (CPSVal
                               (CPSFun
                                (λ v₁ →
                                   CPSVal (CPSFun (λ t''' → CPSIdk x₀ (CPSVar v₁) (CPSVar t'''))))))
                              (CPSVal v))
                             (CPSVal t''))
                          (CPSVar z₄))))
                     (CPSVal (CPSVar z₃))))))))))
     (λ x' → cpsTerm (e₁ x') (CPSIdk x₁) CPSId))
    (λ v → k (CPSVar v) t)
  ⟶⟨ rLet₁ (rLet₁ (rFun (λ x₆ → rFun (λ x₇ → rFun (λ x₈ → rLet₂ (λ x₉ → rBeta
      (tSubst (pcontext-plug p₂ (Val (Var x₆))) (λ t₃ v₂ → sApp Subst≠ (sVal sVar=))))))))) ⟩
  CPSLet
    (CPSLet
     (CPSVal
      (CPSFun
       (λ z →
          CPSVal
          (CPSFun
           (λ z₁ →
              CPSVal
              (CPSFun
               (λ z₂ →
                  CPSLet
                  (CPSVal
                   (CPSAppend refl CPSId (CPSCons x₂ (CPSVar z₁) (CPSVar z₂))))
                  (λ z₃ →
                     cpsTerm (pcontext-plug p₂ (Val (Var z)))
                     (λ v t'' →
                        CPSApp
                        (CPSApp
                         (CPSVal
                          (CPSFun
                           (λ v₁ →
                              CPSVal (CPSFun (λ t''' → CPSIdk x₀ (CPSVar v₁) (CPSVar t'''))))))
                         (CPSVal v))
                        (CPSVal t''))
                     (CPSVar z₃)))))))))
     (λ x' → cpsTerm (e₁ x') (CPSIdk x₁) CPSId))
    (λ v → k (CPSVar v) t)
  ⟶⟨ rLet₁ (rLet₁ (rFun (λ x₆ → rFun (λ x₇ → rFun (λ x₈ → rLet₂ (λ x₉ →
     correctCont (pcontext-plug p₂ (Val (Var x₆)))
       (λ v t'' →
          CPSApp
          (CPSApp
           (CPSVal
            (CPSFun
             (λ v₁ →
                CPSVal (CPSFun (λ t''' → CPSIdk x₀ (CPSVar v₁) (CPSVar t'''))))))
           (CPSVal v))
          (CPSVal t''))
          {k₂ = (λ v t'' →
          CPSApp
            (CPSVal (CPSFun (λ t''' → CPSIdk x₀ v (CPSVar t'''))))
            (CPSVal t''))}
       (λ v t₃ → sApp (sApp Subst≠ (sVal sVar=)) Subst≠)
       λ v t₃ → rApp₁ (rBeta (sVal (sFun (λ x₁₀ → sIdk sVar= SubstV≠)))))))))) ⟩
  CPSLet
    (CPSLet
     (CPSVal
      (CPSFun
       (λ z →
          CPSVal
          (CPSFun
           (λ z₁ →
              CPSVal
              (CPSFun
               (λ z₂ →
                  CPSLet
                  (CPSVal
                   (CPSAppend refl CPSId (CPSCons x₂ (CPSVar z₁) (CPSVar z₂))))
                  (λ z₃ →
                     cpsTerm (pcontext-plug p₂ (Val (Var z)))
                     (λ v t'' →
                        CPSApp (CPSVal (CPSFun (λ t''' → CPSIdk x₀ v (CPSVar t'''))))
                        (CPSVal t''))
                     (CPSVar z₃)))))))))
     (λ x' → cpsTerm (e₁ x') (CPSIdk x₁) CPSId))
    (λ v → k (CPSVar v) t)
  ⟶⟨ rLet₁ (rLet₁ (rFun (λ x₆ → rFun (λ x₇ → rFun (λ x₈ → rLet₂ (λ x₉ →
     correctCont (pcontext-plug p₂ (Val (Var x₆)))
       (λ v t'' →
          CPSApp (CPSVal (CPSFun (λ t''' → CPSIdk x₀ v (CPSVar t'''))))
          (CPSVal t''))
          {k₂ = (λ v t'' →  CPSIdk x₀ v t'' )}
       (λ v t₃ → sApp (sVal (sFun (λ x₁₀ → sIdk sVar= SubstV≠))) Subst≠)
       λ v t₃ → rBeta (sIdk SubstV≠ sVar=))))))) ⟩
  CPSLet
    (CPSLet
     (CPSVal
      (CPSFun
       (λ z →
          CPSVal
          (CPSFun
           (λ z₁ →
              CPSVal
              (CPSFun
               (λ z₂ →
                  CPSLet
                  (CPSVal
                   (CPSAppend refl CPSId (CPSCons x₂ (CPSVar z₁) (CPSVar z₂))))
                  (λ z₃ →
                     cpsTerm (pcontext-plug p₂ (Val (Var z)))
                     (λ v t'' → CPSIdk x₀ v t'') (CPSVar z₃)))))))))
     (λ x' → cpsTerm (e₁ x') (CPSIdk x₁) CPSId))
    (λ v → k (CPSVar v) t)
  ⟶⟨ rLet₁ (rLet₁ (rFun (λ x₆ → rFun (λ x₇ → rFun (λ x₈ → rLet₁ rApdid))))) ⟩
  CPSLet
    (CPSLet
     (CPSVal
      (CPSFun
       (λ z →
          CPSVal
          (CPSFun
           (λ z₁ →
              CPSVal
              (CPSFun
               (λ z₂ →
                  CPSLet (CPSVal (CPSCons x₂ (CPSVar z₁) (CPSVar z₂)))
                  (λ z₃ →
                     cpsTerm (pcontext-plug p₂ (Val (Var z)))
                     (λ v t'' → CPSIdk x₀ v t'') (CPSVar z₃)))))))))
     (λ x' → cpsTerm (e₁ x') (CPSIdk x₁) CPSId))
    (λ v → k (CPSVar v) t)
  ⟶⟨ rLet₁ (rLet₁ (rFun (λ x₆ → rFun (λ x₇ → rFun (λ x₈ → rLet₁ {!rConst!}))))) ⟩
  {!!}
  ⟶⟨ {!!} ⟩
  -- ⟶⟨ rLet₁ (rLet₁ (rFun (λ x₆ → rFun (λ x₇ → rFun (λ x₈ → rLetApp))))) ⟩
  -- CPSLet
  --   (CPSLet
  --    (CPSVal
  --     (CPSFun
  --      (λ z →
  --         CPSVal
  --         (CPSFun
  --          (λ z₁ →
  --             CPSVal
  --             (CPSFun
  --              (λ z₂ →
  --                 CPSApp
  --                 (CPSVal
  --                  (CPSFun
  --                   (λ z₃ →
  --                      cpsTerm (pcontext-plug p₂ (Val (Var z)))
  --                      (λ v t'' → CPSIdk x₀ v t'') (CPSVar z₃))))
  --                 (CPSVal (CPSCons x₂ (CPSVar z₁) (CPSVar z₂))))))))))
  --    (λ x' → cpsTerm (e₁ x') (CPSIdk x₁) CPSId))
  --   (λ v → k (CPSVar v) t)
  -- ⟶⟨ rLet₁ (rLet₁ (rFun (λ x₆ → rFun (λ x₇ → rFun (λ x₈ → rBeta
  --     (tSubst (pcontext-plug p₂ (Val (Var x₆))) (λ t₃ v₂ → sIdk SubstV≠ sVar=))))))) ⟩
  -- CPSLet
  --   (CPSLet
  --    (CPSVal
  --     (CPSFun
  --      (λ z →
  --         CPSVal
  --         (CPSFun
  --          (λ z₁ →
  --             CPSVal
  --             (CPSFun
  --              (λ z₂ →
  --                 cpsTerm (pcontext-plug p₂ (Val (Var z))) (CPSIdk x₀)
  --                 (CPSCons x₂ (CPSVar z₁) (CPSVar z₂)))))))))
  --    (λ x' → cpsTerm (e₁ x') (CPSIdk x₁) CPSId))
  --   (λ v → k (CPSVar v) t)
  --⟶⟨ rLet₁ (rLet₁ (rFun (λ x₆ → rFun (λ x₇ → rFun (λ x₈ → aux (pcontext-plug p₂ (Val (Var x₆))) x₇ x₈))))) ⟩
  CPSLet
    (CPSLet
     (CPSVal
      (CPSFun
       (λ x₆ →
          CPSVal
          (CPSFun
           (λ k' →
              CPSVal
              (CPSFun
               (λ t' →
                  cpsTerm (pcontext-plug p₂ (Val (Var x₆)))
                  (λ v t'' →
                     CPSApp (CPSApp (CPSVal (CPSVar k')) (CPSVal v)) (CPSVal t''))
                  (CPSVar t'))))))))
     (λ z → cpsTerm (e₁ z) (CPSIdk x₁) CPSId))
    (λ v → k (CPSVar v) t)
  ≡⟨ refl ⟩
  CPSLet
    (CPSLet
     (CPSVal
      (CPSFun
       (λ x₆ →
          CPSVal
          (CPSFun
           (λ k' →
              CPSVal
              (CPSFun
               (λ t' →
                  cpsTerm (pcontext-plug p₂ (Val (Var x₆)))
                  (λ v t'' →
                     CPSApp (CPSApp (CPSVal (CPSVar k')) (CPSVal v)) (CPSVal t''))
                  (CPSVar t'))))))))
     (λ z → cpsTerm (e₁ z) (λ v t'' → CPSIdk x₁ v t'') CPSId))
    (λ v → k (CPSVar v) t)
  ⟵⟨ rLet₁ (rLet₂ (λ x₆ →
      correctCont (e₁ x₆)
        (λ v t'' →
           CPSApp (CPSVal (CPSFun (λ t''' → CPSIdk x₁ v (CPSVar t'''))))
           (CPSVal t''))
           {k₂ = (λ v t'' → CPSIdk x₁ v t'')}
        (λ v t₃ → sApp (sVal (sFun (λ x₇ → sIdk sVar= SubstV≠))) Subst≠)
        λ v t₃ → rBeta (sIdk SubstV≠ sVar=))) ⟩
  CPSLet
    (CPSLet
     (CPSVal
      (CPSFun
       (λ x₆ →
          CPSVal
          (CPSFun
           (λ k' →
              CPSVal
              (CPSFun
               (λ t' →
                  cpsTerm (pcontext-plug p₂ (Val (Var x₆)))
                  (λ v t'' →
                     CPSApp (CPSApp (CPSVal (CPSVar k')) (CPSVal v)) (CPSVal t''))
                  (CPSVar t'))))))))
     (λ z →
        cpsTerm (e₁ z)
        (λ v t'' →
           CPSApp (CPSVal (CPSFun (λ t''' → CPSIdk x₁ v (CPSVar t'''))))
           (CPSVal t''))
        CPSId))
    (λ v → k (CPSVar v) t)
  ⟵⟨ rLet₁ (rLet₂ (λ x₆ →
      correctCont (e₁ x₆)
        (λ v t'' →
           CPSApp
           (CPSApp
            (CPSVal
             (CPSFun
              (λ v₁ →
                 CPSVal (CPSFun (λ t''' → CPSIdk x₁ (CPSVar v₁) (CPSVar t'''))))))
            (CPSVal v))
           (CPSVal t''))
           {k₂ = (λ v t'' →
          CPSApp
           (CPSVal (CPSFun (λ t''' → CPSIdk x₁ v (CPSVar t'''))))
           (CPSVal t''))}
        (λ v t₃ → sApp (sApp Subst≠ (sVal sVar=)) Subst≠)
        λ v t₃ → rApp₁ (rBeta (sVal (sFun (λ x₇ → sIdk sVar= SubstV≠)))))) ⟩
  CPSLet
    (CPSLet
     (CPSVal
      (CPSFun
       (λ x₆ →
          CPSVal
          (CPSFun
           (λ k' →
              CPSVal
              (CPSFun
               (λ t' →
                  cpsTerm (pcontext-plug p₂ (Val (Var x₆)))
                  (λ v t'' →
                     CPSApp (CPSApp (CPSVal (CPSVar k')) (CPSVal v)) (CPSVal t''))
                  (CPSVar t'))))))))
     (λ z →
        cpsTerm (e₁ z)
        (λ v t'' →
           CPSApp
           (CPSApp
            (CPSVal
             (CPSFun
              (λ v₁ →
                 CPSVal (CPSFun (λ t''' → CPSIdk x₁ (CPSVar v₁) (CPSVar t'''))))))
            (CPSVal v))
           (CPSVal t''))
        CPSId))
    (λ v → k (CPSVar v) t)
  ⟵⟨ rLet₁ (rLet₂ (λ x₆ → rBeta (tSubst (e₁ x₆) (λ t₃ v₂ → sApp Subst≠ (sVal sVar=))))) ⟩
  CPSLet
    (CPSLet
     (CPSVal
      (CPSFun
       (λ x₆ →
          CPSVal
          (CPSFun
           (λ k' →
              CPSVal
              (CPSFun
               (λ t' →
                  cpsTerm (pcontext-plug p₂ (Val (Var x₆)))
                  (λ v t'' →
                     CPSApp (CPSApp (CPSVal (CPSVar k')) (CPSVal v)) (CPSVal t''))
                  (CPSVar t'))))))))
     (λ x₆ →
        CPSApp
        (CPSVal
         (CPSFun
          (λ z₁ →
             cpsTerm (e₁ x₆)
             (λ v t'' →
                CPSApp
                (CPSApp
                 (CPSVal
                  (CPSFun
                   (λ v₁ →
                      CPSVal (CPSFun (λ t''' → CPSIdk x₁ (CPSVar v₁) (CPSVar t'''))))))
                 (CPSVal v))
                (CPSVal t''))
             (CPSVar z₁))))
        (CPSVal CPSId)))
    (λ v → k (CPSVar v) t)
  ⟵⟨ rLet₁ rLet₃ ⟩
  CPSLet
    (CPSApp
     (CPSLet
      (CPSVal
       (CPSFun
        (λ x₆ →
           CPSVal
           (CPSFun
            (λ k' →
               CPSVal
               (CPSFun
                (λ t' →
                   cpsTerm (pcontext-plug p₂ (Val (Var x₆)))
                   (λ v t'' →
                      CPSApp (CPSApp (CPSVal (CPSVar k')) (CPSVal v)) (CPSVal t''))
                   (CPSVar t'))))))))
      (λ z →
         CPSVal
         (CPSFun
          (λ z₁ →
             cpsTerm (e₁ z)
             (λ v t'' →
                CPSApp
                (CPSApp
                 (CPSVal
                  (CPSFun
                   (λ v₁ →
                      CPSVal (CPSFun (λ t''' → CPSIdk x₁ (CPSVar v₁) (CPSVar t'''))))))
                 (CPSVal v))
                (CPSVal t''))
             (CPSVar z₁)))))
     (CPSVal CPSId))
    (λ v → k (CPSVar v) t)
  ⟵⟨ rLet₁ (rApp₁ (rLet₂ (λ x₆ → rBeta (sVal (sFun (λ x₇ →
     kSubst (e₁ x₆)
       (λ y →
          λ v t'' → CPSApp (CPSApp (CPSVal y) (CPSVal v)) (CPSVal t''))
       (λ x₈ t₃ → sApp (sApp (sVal sVar=) Subst≠) Subst≠))))))) ⟩
  CPSLet
    (CPSApp
     (CPSLet
      (CPSVal
       (CPSFun
        (λ x₆ →
           CPSVal
           (CPSFun
            (λ k' →
               CPSVal
               (CPSFun
                (λ t' →
                   cpsTerm (pcontext-plug p₂ (Val (Var x₆)))
                   (λ v t'' →
                      CPSApp (CPSApp (CPSVal (CPSVar k')) (CPSVal v)) (CPSVal t''))
                   (CPSVar t'))))))))
      (λ x₆ →
         CPSApp
         (CPSVal
          (CPSFun
           (λ k' →
              CPSVal
              (CPSFun
               (λ t' →
                  cpsTerm (e₁ x₆)
                  (λ v t'' →
                     CPSApp (CPSApp (CPSVal (CPSVar k')) (CPSVal v)) (CPSVal t''))
                  (CPSVar t'))))))
         (CPSVal
          (CPSFun
           (λ v →
              CPSVal (CPSFun (λ t'' → CPSIdk x₁ (CPSVar v) (CPSVar t''))))))))
     (CPSVal CPSId))
    (λ v → k (CPSVar v) t)
  ⟵⟨ rLet₁ (rApp₁ rLet₃) ⟩
  CPSLet
    (CPSApp
     (CPSApp
      (CPSLet
       (CPSVal
        (CPSFun
         (λ x₆ →
            CPSVal
            (CPSFun
             (λ k' →
                CPSVal
                (CPSFun
                 (λ t' →
                    cpsTerm (pcontext-plug p₂ (Val (Var x₆)))
                    (λ v t'' →
                       CPSApp (CPSApp (CPSVal (CPSVar k')) (CPSVal v)) (CPSVal t''))
                    (CPSVar t'))))))))
       (λ x₆ →
          CPSVal
          (CPSFun
           (λ k' →
              CPSVal
              (CPSFun
               (λ t' →
                  cpsTerm (e₁ x₆)
                  (λ v t'' →
                     CPSApp (CPSApp (CPSVal (CPSVar k')) (CPSVal v)) (CPSVal t''))
                  (CPSVar t')))))))
      (CPSVal
       (CPSFun
        (λ v →
           CPSVal (CPSFun (λ t'' → CPSIdk x₁ (CPSVar v) (CPSVar t'')))))))
     (CPSVal CPSId))
    (λ v → k (CPSVar v) t)
  ⟶⟨ rLet₁ (rApp₁ (rApp₁ rLetApp)) ⟩
  (CPSLet
       (CPSApp
        (CPSApp
         (CPSApp
          (CPSVal
           (CPSFun
            (λ x₆ →
               CPSVal
               (CPSFun
                (λ k' →
                   CPSVal
                   (CPSFun
                    (λ t' →
                       cpsTerm (e₁ x₆)
                       (λ v t'' →
                          CPSApp (CPSApp (CPSVal (CPSVar k')) (CPSVal v)) (CPSVal t''))
                       (CPSVar t'))))))))
          (CPSVal
           (CPSFun
            (λ x₆ →
               CPSVal
               (CPSFun
                (λ k' →
                   CPSVal
                   (CPSFun
                    (λ t' →
                       cpsTerm (pcontext-plug p₂ (Val (Var x₆)))
                       (λ v t'' →
                          CPSApp (CPSApp (CPSVal (CPSVar k')) (CPSVal v)) (CPSVal t''))
                       (CPSVar t')))))))))
         (CPSVal
          (CPSFun
           (λ v →
              CPSVal (CPSFun (λ t'' → CPSIdk x₁ (CPSVar v) (CPSVar t'')))))))
        (CPSVal CPSId))
       (λ v → k (CPSVar v) t))

  ∎
  

correctEta {var} {τ₁} {α} {.α} {μα} {.μα} {.(Prompt x₀ (pcontext-plug p₁ (Control x₁ x₂ x₃ e₁)))} {.(Prompt x₁ (App (Val (Fun e₁)) (Val (Fun (λ x₈ → pcontext-plug p₂ (Val (Var x₈)))))))} k t sch sch' (RControl {τ = τ} {α' = α'} {β = τ₁} {β' = β'} {γ = γ} {γ' = γ'} {t₁ = t₁} {t₂ = t₂} {τ₂ = α} {τ₃ = τ₃} {τ₄ = τ₄} {τ₅ = τ₅} {μ₀ = x₄ ⇒ x₅ , μ₀} {μ₁ = μ₁} {μᵢ = μᵢ} {μα' = μα'} {μβ = μβ} {μβ' = μβ'} {μ₂ = μ₂} {μ₃ = x₆ ⇒ x₇ , μ₃} {μ₄ = μ₄} {μ₅ = μ₅} p₁ p₂ {x₀} x₁ x₂ x₃ x e₁) = {!!} --}

-- correctEta : {var : cpstyp → Set} {τ₁ α β : typ} {μα μβ : trail}
--              {μs : trails[ μβ ] μα} →
--              {e e′ : term[ var ∘ cpsT ] τ₁ ⟨ μs ⟩ α ⟨ μβ ⟩ β} →
--              (k : cpsvalue[ var ] (cpsT τ₁) → cpsvalue[ var ] (cpsMs μs)
--              → cpsterm[ var ] (cpsT α)) →
--              (t : cpsvalue[ var ] (cpsM μβ)) →
--              schematicV k →
--              schematicV′ k →
--              Reduce e e′ →
--              cpsreduce (cpsTerm e k t) (cpsTerm e′ k t)
             

correctEta {var} {τ₁} {α} {.α} {μα} {.μα} {μs}
           {.(Prompt id₀ (pcontext-plug p₁ (Control id c₁ c₂ e)))}
           {.(Prompt id (App (Val (Fun e)) (Val (Fun (λ x₂ → pcontext-plug p₂ (Val (Var x₂)))))))}
           k t sch sch'
           (RControl p₁ p₂ {id₀} id c₁ c₂ x e) = begin
    (CPSLet
       (cpsTerm (pcontext-plug p₁ (Control id c₁ c₂ e)) (CPSIdk id₀)
        CPSId)
       (λ v → k (CPSVar v) t))

  ⟶⟨ rLet₁ (control-lemma p₁ ? id c₁ c₂ x e (CPSIdk id₀) CPSId (λ v t₃ → sIdk sVar= SubstV≠) λ t₃ v₂ → sIdk SubstV≠ sVar=) ⟩
  CPSLet
    (cpsTerm
     (App (Val (Fun (λ x₄ → pcontext-plug p₂ (Val (Var x₄)))))
      (Control c₁ c₂ refl e))
     (CPSIdk id₀) CPSId)
    (λ v → k (CPSVar v) t)
  ⟶⟨ rLet₁ (rLet₁ (rFun (λ x₄ → rFun (λ x₅ → rFun (λ x₆ → rLet₂ (λ x₇ → rApp₁ (rApp₁ (rBeta
      (sVal (sFun (λ x₈ → sVal (sFun (λ x₉ → eSubst (subst-context p₂ (Var x₄))
      (λ x₁₀ → sApp (sApp Subst≠ (sVal x₁₀)) Subst≠)))))))))))))) ⟩
  CPSLet
    (CPSLet
     (CPSVal
      (CPSFun
       (λ z →
          CPSVal
          (CPSFun
           (λ z₁ →
              CPSVal
              (CPSFun
               (λ z₂ →
                  CPSLet
                  (CPSVal (CPSAppend refl CPSId
                   (CPSCons ? (CPSVar z₁)
                    (CPSVar z₂))))
                  (λ z₃ →
                     CPSApp
                     (CPSApp
                      (CPSVal
                       (CPSFun
                        (λ z₄ →
                           CPSVal
                           (CPSFun
                            (λ z₅ →
                               cpsTerm (pcontext-plug p₂ (Val (Var z)))
                               (λ v t'' →
                                  CPSApp (CPSApp (CPSVal (CPSVar z₄)) (CPSVal v)) (CPSVal t''))
                               (CPSVar z₅))))))
                      (CPSVal
                       (CPSFun
                        (λ v →
                           CPSVal (CPSFun (λ t'' → CPSIdk id₀ (CPSVar v) (CPSVar t'')))))))
                     (CPSVal (CPSVar z₃))))))))))
     (λ x' → cpsTerm (e x') (CPSIdk ?) CPSId))
    (λ v → k (CPSVar v) t)

  ⟶⟨ rLet₁ (rLet₁ (rFun (λ x₄ → rFun (λ x₅ → rFun (λ x₆ → rLet₂ (λ x₇ → rApp₁ (rBeta
      (sVal (sFun (λ x₈ →
      kSubst (pcontext-plug p₂ (Val (Var x₄)))
        (λ y →
           λ v t'' → CPSApp (CPSApp (CPSVal y) (CPSVal v)) (CPSVal t''))
        (λ x₉ t₃ → sApp (sApp (sVal sVar=) Subst≠) Subst≠))))))))))) ⟩
  CPSLet
    (CPSLet
     (CPSVal
      (CPSFun
       (λ z →
          CPSVal
          (CPSFun
           (λ z₁ →
              CPSVal
              (CPSFun
               (λ z₂ →
                  CPSLet
                  (CPSVal (CPSAppend refl CPSId
                   (CPSCons ? (CPSVar z₁)
                    (CPSVar z₂))))
                  (λ z₃ →
                     CPSApp
                     (CPSVal
                      (CPSFun
                       (λ z₄ →
                          cpsTerm (pcontext-plug p₂ (Val (Var z)))
                          (λ v t'' →
                             CPSApp
                             (CPSApp
                              (CPSVal
                               (CPSFun
                                (λ v₁ →
                                   CPSVal (CPSFun (λ t''' → CPSIdk ? (CPSVar v₁) (CPSVar t'''))))))
                              (CPSVal v))
                             (CPSVal t''))
                          (CPSVar z₄))))
                     (CPSVal (CPSVar z₃))))))))))
     (λ x' → cpsTerm (e x') (CPSIdk ?) CPSId))
    (λ v → k (CPSVar v) t)
  ⟶⟨ rLet₁ (rLet₁ (rFun (λ x₄ → rFun (λ x₅ → rFun (λ x₆ → rLet₂ (λ x₇ → rBeta
      (tSubst (pcontext-plug p₂ (Val (Var x₄)))
      (λ t₃ v₂ → sApp Subst≠ (sVal sVar=))))))))) ⟩
  CPSLet
    (CPSLet
     (CPSVal
      (CPSFun
       (λ z →
          CPSVal
          (CPSFun
           (λ z₁ →
              CPSVal
              (CPSFun
               (λ z₂ →
                  CPSLet
                  (CPSVal (CPSAppend refl CPSId
                   (CPSCons ? (CPSVar z₁)
                    (CPSVar z₂))))
                  (λ z₃ →
                     cpsTerm (pcontext-plug p₂ (Val (Var z)))
                     (λ v t'' →
                        CPSApp
                        (CPSApp
                         (CPSVal
                          (CPSFun
                           (λ v₁ →
                              CPSVal (CPSFun (λ t''' → CPSIdk ? (CPSVar v₁) (CPSVar t'''))))))
                         (CPSVal v))
                        (CPSVal t''))
                     (CPSVar z₃)))))))))
     (λ x' → cpsTerm (e x') (CPSIdk ?) CPSId))
    (λ v → k (CPSVar v) t)
  ⟶⟨ rLet₁ (rLet₁ (rFun (λ x₄ → rFun (λ x₅ → rFun (λ x₆ → rLet₂ (λ x₇ →
      correctCont (pcontext-plug p₂ (Val (Var x₄)))
        (λ v t'' →
           CPSApp
           (CPSApp
            (CPSVal
             (CPSFun
              (λ v₁ →
                 CPSVal (CPSFun (λ t''' → CPSIdk ? (CPSVar v₁) (CPSVar t'''))))))
            (CPSVal v))
           (CPSVal t''))
           {k₂ = (λ v t'' →
           CPSApp
           (CPSVal (CPSFun (λ t''' → CPSIdk ? v (CPSVar t'''))))
           (CPSVal t''))}
        (λ v t₃ → sApp (sApp Subst≠ (sVal sVar=)) Subst≠)
        λ v t₃ → rApp₁ (rBeta (sVal (sFun (λ x₈ → sIdk sVar= SubstV≠)))))))))) ⟩
  CPSLet
    (CPSLet
     (CPSVal
      (CPSFun
       (λ z →
          CPSVal
          (CPSFun
           (λ z₁ →
              CPSVal
              (CPSFun
               (λ z₂ →
                  CPSLet
                  (CPSVal (CPSAppend refl CPSId
                   (CPSCons ? (CPSVar z₁)
                    (CPSVar z₂))))
                  (λ z₃ →
                     cpsTerm (pcontext-plug p₂ (Val (Var z)))
                     (λ v t'' →
                        CPSApp (CPSVal (CPSFun (λ t''' → CPSIdk ? v (CPSVar t'''))))
                        (CPSVal t''))
                     (CPSVar z₃)))))))))
     (λ x' → cpsTerm (e x') (CPSIdk ?) CPSId))
    (λ v → k (CPSVar v) t)
  ⟶⟨ rLet₁ (rLet₁ (rFun (λ x₄ → rFun (λ x₅ → rFun (λ x₆ → rLet₂ (λ x₇ →
      correctCont (pcontext-plug p₂ (Val (Var x₄)))
        (λ v t'' →
           CPSApp (CPSVal (CPSFun (λ t''' → CPSIdk ? v (CPSVar t'''))))
           (CPSVal t''))
           {k₂ = (λ v t'' → CPSIdk ? v t'')}
        (λ v t₃ → sApp (sVal (sFun (λ x₈ → sIdk sVar= SubstV≠))) Subst≠)
        λ v t₃ → rBeta (sIdk SubstV≠ sVar=))))))) ⟩
  CPSLet
    (CPSLet
     (CPSVal
      (CPSFun
       (λ z →
          CPSVal
          (CPSFun
           (λ z₁ →
              CPSVal
              (CPSFun
               (λ z₂ →
                  CPSLet
                  (CPSVal (CPSAppend refl CPSId
                   (CPSCons ? (CPSVar z₁)
                    (CPSVar z₂))))
                  (λ z₃ →
                     cpsTerm (pcontext-plug p₂ (Val (Var z)))
                     (λ v t'' → CPSIdk ? v t'') (CPSVar z₃)))))))))
     (λ x' → cpsTerm (e x') (CPSIdk ?) CPSId))
    (λ v → k (CPSVar v) t)
  ⟶⟨ rLet₁ (rLet₁ (rFun (λ x₄ → rFun (λ x₅ → rFun (λ x₆ → rLet₁ rApdid))))) ⟩
  CPSLet
    (CPSLet
     (CPSVal
      (CPSFun
       (λ z →
          CPSVal
          (CPSFun
           (λ z₁ →
              CPSVal
              (CPSFun
               (λ z₂ →
                  CPSLet (CPSVal (CPSCons ? (CPSVar z₁) (CPSVar z₂)))
                  (λ z₃ →
                     cpsTerm (pcontext-plug p₂ (Val (Var z)))
                     (λ v t'' → CPSIdk ? v t'') (CPSVar z₃)))))))))
     (λ x' → cpsTerm (e x') (CPSIdk ?) CPSId))
    (λ v → k (CPSVar v) t)
  --rConst先にやる？
  -- ⟶⟨ rLet₁ (rLet₁ (rFun (λ x₆ → rFun (λ x₇ → rFun (λ x₈ → rLet₁ rConst))))) ⟩
  -- CPSLet
  --   (CPSLet
  --    (CPSVal
  --     (CPSFun
  --      (λ z →
  --         CPSVal
  --         (CPSFun
  --          (λ z₁ →
  --             CPSVal
  --             (CPSFun
  --              (λ z₂ →
  --                 CPSLet
  --                 (CPSVal
  --                  (CPSFun
  --                   (λ v →
  --                      CPSVal
  --                      (CPSFun
  --                       (λ t' →
  --                          CPSApp (CPSApp (CPSVal (CPSVar z₁)) (CPSVal (CPSVar v)))
  --                          (CPSVal (CPSCons x₂ (CPSVar z₂) (CPSVar t'))))))))
  --                 (λ z₃ →
  --                    cpsTerm (pcontext-plug p₂ (Val (Var z)))
  --                    (λ v t'' → CPSIdk x₀ v t'') (CPSVar z₃)))))))))
  --    (λ x' → cpsTerm (e₁ x') (CPSIdk x₁) CPSId))
  --   (λ v → k (CPSVar v) t)
  -- ⟶⟨ rLet₁ (rLet₁ (rFun λ x₆ → rFun (λ x₇ → rFun (λ x₈ → rLetApp)))) ⟩
  -- CPSLet
  --   (CPSLet
  --    (CPSVal
  --     (CPSFun
  --      (λ z →
  --         CPSVal
  --         (CPSFun
  --          (λ z₁ →
  --             CPSVal
  --             (CPSFun
  --              (λ z₂ →
  --                 CPSApp
  --                 (CPSVal
  --                  (CPSFun
  --                   (λ z₃ →
  --                      cpsTerm (pcontext-plug p₂ (Val (Var z)))
  --                      (λ v t'' → CPSIdk x₀ v t'') (CPSVar z₃))))
  --                 (CPSVal
  --                  (CPSFun
  --                   (λ v →
  --                      CPSVal
  --                      (CPSFun
  --                       (λ t' →
  --                          CPSApp (CPSApp (CPSVal (CPSVar z₁)) (CPSVal (CPSVar v)))
  --                          (CPSVal (CPSCons x₂ (CPSVar z₂) (CPSVar t')))))))))))))))
  --    (λ x' → cpsTerm (e₁ x') (CPSIdk x₁) CPSId))
  --   (λ v → k (CPSVar v) t)
  -- ⟶⟨ rLet₁ (rLet₁ (rFun (λ x₆ → rFun (λ x₇ → rFun (λ x₈ → rBeta
  --    (tSubst (pcontext-plug p₂ (Val (Var x₆))) (λ t₃ v₂ → sIdk SubstV≠ sVar=))))))) ⟩
  -- CPSLet
  --   (CPSLet
  --    (CPSVal
  --     (CPSFun
  --      (λ z →
  --         CPSVal
  --         (CPSFun
  --          (λ z₁ →
  --             CPSVal
  --             (CPSFun
  --              (λ z₂ →
  --                 cpsTerm (pcontext-plug p₂ (Val (Var z))) (CPSIdk x₀)
  --                 (CPSFun
  --                  (λ v →
  --                     CPSVal
  --                     (CPSFun
  --                      (λ t' →
  --                         CPSApp (CPSApp (CPSVal (CPSVar z₁)) (CPSVal (CPSVar v)))
  --                         (CPSVal (CPSCons x₂ (CPSVar z₂) (CPSVar t'))))))))))))))
  --    (λ x' → cpsTerm (e₁ x') (CPSIdk x₁) CPSId))
  --   (λ v → k (CPSVar v) t)
  --⟶⟨ rLet₁ (rLet₁ (rFun (λ x₆ → rFun (λ x₇ → rFun (λ x₈ → {!aux₃ (pcontext-plug p₂ (Val (Var x₆))) ? x₈!}))))) ⟩
  ⟶⟨ rLet₁ (rLet₁ (rFun (λ x₄ → rFun (λ x₅ → rFun (λ x₆ → rLetApp))))) ⟩
  CPSLet
    (CPSLet
     (CPSVal
      (CPSFun
       (λ z →
          CPSVal
          (CPSFun
           (λ z₁ →
              CPSVal
              (CPSFun
               (λ z₂ →
                  CPSApp
                  (CPSVal
                   (CPSFun
                    (λ z₃ →
                       cpsTerm (pcontext-plug p₂ (Val (Var z)))
                       (λ v t'' → CPSIdk ? v t'') (CPSVar z₃))))
                  (CPSVal (CPSCons ? (CPSVar z₁) (CPSVar z₂))))))))))
     (λ x' → cpsTerm (e x') (CPSIdk ?) CPSId))
    (λ v → k (CPSVar v) t)
  ⟶⟨ rLet₁ (rLet₁ (rFun (λ x₄ → rFun (λ x₅ → rFun (λ x₆ → rBeta
     (tSubst (pcontext-plug p₂ (Val (Var x₄))) (λ t₃ v₂ → sIdk SubstV≠ sVar=))))))) ⟩
  CPSLet
    (CPSLet
     (CPSVal
      (CPSFun
       (λ z →
          CPSVal
          (CPSFun
           (λ z₁ →
              CPSVal
              (CPSFun
               (λ z₂ →
                  cpsTerm (pcontext-plug p₂ (Val (Var z))) (CPSIdk ?)
                  (CPSCons ? (CPSVar z₁) (CPSVar z₂)))))))))
     (λ x' → cpsTerm (e x') (CPSIdk ?) CPSId))
    (λ v → k (CPSVar v) t)
  --⟶⟨ rLet₁ (rLet₁ (rFun (λ x₄ → rFun (λ x₅ → rFun (λ x₆ → {!aux p₂ x₄ x₅ x₆!}))))) ⟩
  ⟶⟨ ? ⟩
  --rLet₁ (rLet₁ (rFun (λ x₄ → rFun (λ x₅ → rFun (λ x₆ → (let (c' , red) = aux₄ (pcontext-plug p₂ (Val (Var x₄))) (CPSIdk x₀) x₅ x₆ in {!!}))))))
  CPSLet
    (CPSLet
     (CPSVal
      (CPSFun
       (λ z →
          CPSVal
          (CPSFun
           (λ z₁ →
              CPSVal
              (CPSFun
               (λ z₂ →
                  cpsTerm (pcontext-plug p₂ (Val (Var z)))
                  (λ v t' →
                     CPSIdk ? v
                     (CPSCons
                      (proj₁ (? (pcontext-plug p₂ (Val (Var z))) (CPSIdk ?) z₁ z₂))
                      (CPSVar z₁) t'))
                  (CPSVar z₂))))))))
     (λ x' → cpsTerm (e x') (CPSIdk ?) CPSId))
    (λ v → k (CPSVar v) t)
  ⟵⟨ rLet₁ (rLet₁ (rFun (λ x₇ → rFun (λ x₈ → rFun (λ x₉ → {!!}))))) ⟩
  CPSLet
    (CPSLet
     (CPSVal
      (CPSFun
       (λ x₄ →
          CPSVal
          (CPSFun
           (λ k' →
              CPSVal
              (CPSFun
               (λ t' →
                  cpsTerm (pcontext-plug p₂ (Val (Var x₄)))
                  (λ v t'' →
                     CPSApp (CPSApp (CPSVal (CPSVar k')) (CPSVal v)) (CPSVal t''))
                  (CPSVar t'))))))))
     (λ z → cpsTerm (e z) (CPSIdk ?) CPSId))
    (λ v → k (CPSVar v) t)
  ≡⟨ refl ⟩
  CPSLet
    (CPSLet
     (CPSVal
      (CPSFun
       (λ x₄ →
          CPSVal
          (CPSFun
           (λ k' →
              CPSVal
              (CPSFun
               (λ t' →
                  cpsTerm (pcontext-plug p₂ (Val (Var x₄)))
                  (λ v t'' →
                     CPSApp (CPSApp (CPSVal (CPSVar k')) (CPSVal v)) (CPSVal t''))
                  (CPSVar t'))))))))
     (λ z → cpsTerm (e z) (λ v t'' → CPSIdk ? v t'') CPSId))
    (λ v → k (CPSVar v) t)
  ⟵⟨ rLet₁ (rLet₂ (λ x₄ →
      correctCont (e x₄)
        (λ v t'' →
           CPSApp (CPSVal (CPSFun (λ t''' → CPSIdk ? v (CPSVar t'''))))
           (CPSVal t''))
           {k₂ = (λ v t'' → CPSIdk ? v t'')}
        (λ v t₃ → sApp (sVal (sFun (λ x₅ → sIdk sVar= SubstV≠))) Subst≠)
        λ v t₃ → rBeta (sIdk SubstV≠ sVar=))) ⟩
  CPSLet
    (CPSLet
     (CPSVal
      (CPSFun
       (λ x₄ →
          CPSVal
          (CPSFun
           (λ k' →
              CPSVal
              (CPSFun
               (λ t' →
                  cpsTerm (pcontext-plug p₂ (Val (Var x₄)))
                  (λ v t'' →
                     CPSApp (CPSApp (CPSVal (CPSVar k')) (CPSVal v)) (CPSVal t''))
                  (CPSVar t'))))))))
     (λ z →
        cpsTerm (e z)
        (λ v t'' →
           CPSApp (CPSVal (CPSFun (λ t''' → CPSIdk ? v (CPSVar t'''))))
           (CPSVal t''))
        CPSId))
    (λ v → k (CPSVar v) t)
  ⟵⟨ rLet₁ (rLet₂ (λ x₄ →
      correctCont (e x₄)
        (λ v t'' →
           CPSApp
           (CPSApp
            (CPSVal
             (CPSFun
              (λ v₁ →
                 CPSVal (CPSFun (λ t''' → CPSIdk ? (CPSVar v₁) (CPSVar t'''))))))
            (CPSVal v))
           (CPSVal t''))
           {k₂ = (λ v t'' →
          CPSApp
            (CPSVal (CPSFun (λ t''' → CPSIdk ? v (CPSVar t'''))))
            (CPSVal t''))}
        (λ v t₃ → sApp (sApp Subst≠ (sVal sVar=)) Subst≠)
        λ v t₃ → rApp₁ (rBeta (sVal (sFun (λ x₅ → sIdk sVar= SubstV≠)))))) ⟩
  CPSLet
    (CPSLet
     (CPSVal
      (CPSFun
       (λ x₄ →
          CPSVal
          (CPSFun
           (λ k' →
              CPSVal
              (CPSFun
               (λ t' →
                  cpsTerm (pcontext-plug p₂ (Val (Var x₄)))
                  (λ v t'' →
                     CPSApp (CPSApp (CPSVal (CPSVar k')) (CPSVal v)) (CPSVal t''))
                  (CPSVar t'))))))))
     (λ z →
        cpsTerm (e z)
        (λ v t'' →
           CPSApp
           (CPSApp
            (CPSVal
             (CPSFun
              (λ v₁ →
                 CPSVal (CPSFun (λ t''' → CPSIdk ? (CPSVar v₁) (CPSVar t'''))))))
            (CPSVal v))
           (CPSVal t''))
        CPSId))
    (λ v → k (CPSVar v) t)
  ⟵⟨ rLet₁ (rLet₂ (λ x₄ → rBeta
      (tSubst (e x₄) (λ t₃ v₂ → sApp Subst≠ (sVal sVar=))))) ⟩
  CPSLet
    (CPSLet
     (CPSVal
      (CPSFun
       (λ x₄ →
          CPSVal
          (CPSFun
           (λ k' →
              CPSVal
              (CPSFun
               (λ t' →
                  cpsTerm (pcontext-plug p₂ (Val (Var x₄)))
                  (λ v t'' →
                     CPSApp (CPSApp (CPSVal (CPSVar k')) (CPSVal v)) (CPSVal t''))
                  (CPSVar t'))))))))
     (λ x₄ →
        CPSApp
        (CPSVal
         (CPSFun
          (λ z →
             cpsTerm (e x₄)
             (λ v t'' →
                CPSApp
                (CPSApp
                 (CPSVal
                  (CPSFun
                   (λ v₁ →
                      CPSVal (CPSFun (λ t''' → CPSIdk ? (CPSVar v₁) (CPSVar t'''))))))
                 (CPSVal v))
                (CPSVal t''))
             (CPSVar z))))
        (CPSVal CPSId)))
    (λ v → k (CPSVar v) t)
  ⟵⟨ rLet₁ rLet₃ ⟩
  CPSLet
    (CPSApp
     (CPSLet
      (CPSVal
       (CPSFun
        (λ x₄ →
           CPSVal
           (CPSFun
            (λ k' →
               CPSVal
               (CPSFun
                (λ t' →
                   cpsTerm (pcontext-plug p₂ (Val (Var x₄)))
                   (λ v t'' →
                      CPSApp (CPSApp (CPSVal (CPSVar k')) (CPSVal v)) (CPSVal t''))
                   (CPSVar t'))))))))
      (λ z →
         CPSVal
         (CPSFun
          (λ z₁ →
             cpsTerm (e z)
             (λ v t'' →
                CPSApp
                (CPSApp
                 (CPSVal
                  (CPSFun
                   (λ v₁ →
                      CPSVal (CPSFun (λ t''' → CPSIdk ? (CPSVar v₁) (CPSVar t'''))))))
                 (CPSVal v))
                (CPSVal t''))
             (CPSVar z₁)))))
     (CPSVal CPSId))
    (λ v → k (CPSVar v) t)
  ⟵⟨ rLet₁ (rApp₁ (rLet₂ (λ x₄ → rBeta (sVal (sFun (λ x₅ →
      kSubst (e x₄)
        (λ y →
           λ v t'' → CPSApp (CPSApp (CPSVal y) (CPSVal v)) (CPSVal t''))
        (λ x₆ t₃ → sApp (sApp (sVal sVar=) Subst≠) Subst≠))))))) ⟩
  CPSLet
    (CPSApp
     (CPSLet
      (CPSVal
       (CPSFun
        (λ x₄ →
           CPSVal
           (CPSFun
            (λ k' →
               CPSVal
               (CPSFun
                (λ t' →
                   cpsTerm (pcontext-plug p₂ (Val (Var x₄)))
                   (λ v t'' →
                      CPSApp (CPSApp (CPSVal (CPSVar k')) (CPSVal v)) (CPSVal t''))
                   (CPSVar t'))))))))
      (λ x₄ →
         CPSApp
         (CPSVal
          (CPSFun
           (λ k' →
              CPSVal
              (CPSFun
               (λ t' →
                  cpsTerm (e x₄)
                  (λ v t'' →
                     CPSApp (CPSApp (CPSVal (CPSVar k')) (CPSVal v)) (CPSVal t''))
                  (CPSVar t'))))))
         (CPSVal
          (CPSFun
           (λ v →
              CPSVal (CPSFun (λ t'' → CPSIdk ? (CPSVar v) (CPSVar t''))))))))
     (CPSVal CPSId))
    (λ v → k (CPSVar v) t)
  ⟵⟨ rLet₁ (rApp₁ rLet₃) ⟩
  CPSLet
    (CPSApp
     (CPSApp
      (CPSLet
       (CPSVal
        (CPSFun
         (λ x₄ →
            CPSVal
            (CPSFun
             (λ k' →
                CPSVal
                (CPSFun
                 (λ t' →
                    cpsTerm (pcontext-plug p₂ (Val (Var x₄)))
                    (λ v t'' →
                       CPSApp (CPSApp (CPSVal (CPSVar k')) (CPSVal v)) (CPSVal t''))
                    (CPSVar t'))))))))
       (λ x₄ →
          CPSVal
          (CPSFun
           (λ k' →
              CPSVal
              (CPSFun
               (λ t' →
                  cpsTerm (e x₄)
                  (λ v t'' →
                     CPSApp (CPSApp (CPSVal (CPSVar k')) (CPSVal v)) (CPSVal t''))
                  (CPSVar t')))))))
      (CPSVal
       (CPSFun
        (λ v →
           CPSVal (CPSFun (λ t'' → CPSIdk ? (CPSVar v) (CPSVar t'')))))))
     (CPSVal CPSId))
    (λ v → k (CPSVar v) t)
  ⟶⟨ rLet₁ (rApp₁ (rApp₁ rLetApp)) ⟩
  (CPSLet
       (CPSApp
        (CPSApp
         (CPSApp
          (CPSVal
           (CPSFun
            (λ x₄ →
               CPSVal
               (CPSFun
                (λ k' →
                   CPSVal
                   (CPSFun
                    (λ t' →
                       cpsTerm (e x₄)
                       (λ v t'' →
                          CPSApp (CPSApp (CPSVal (CPSVar k')) (CPSVal v)) (CPSVal t''))
                       (CPSVar t'))))))))
          (CPSVal
           (CPSFun
            (λ x₄ →
               CPSVal
               (CPSFun
                (λ k' →
                   CPSVal
                   (CPSFun
                    (λ t' →
                       cpsTerm (pcontext-plug p₂ (Val (Var x₄)))
                       (λ v t'' →
                          CPSApp (CPSApp (CPSVal (CPSVar k')) (CPSVal v)) (CPSVal t''))
                       (CPSVar t')))))))))
         (CPSVal
          (CPSFun
           (λ v →
              CPSVal (CPSFun (λ t'' → CPSIdk ? (CPSVar v) (CPSVar t'')))))))
        (CPSVal CPSId))
       (λ v → k (CPSVar v) t))
  ∎-}
