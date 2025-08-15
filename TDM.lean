import Init.Data.Nat.Basic
import Mathlib.Data.List.Chain
import Mathlib.Order.Basic


-- @see [[https://dl.acm.org/doi/pdf/10.1145/38713.38760]]
-- LOGICAL MODELING OF TEMPORALDATA という論文の仕様検証


/-- Temporal Data Value
時系列データ値　オブジェクト識別値としてのサロゲート、時刻、属性値を持つ
同一サロゲートに属するデータ値は、時間に沿って全順序を持つ。 <- この制約はTDVじゃなくてTS側の制約では？
⟨s,t,a⟩　と表記する 非時系列データの場合はtは現在時刻として省略される
-/
structure TDV (S : Type u) (T : Type w) (A : Type v) [LinearOrder T] where
  s: S
  t: T
  a: A

/-- Time Stamp
特定のオブジェクトに対応する、順序付きの時系列データ値の集まり。

⟨s,(t,a)∗⟩ と表記する　(t,a)^* は時刻と値のペアの列。
-/
structure TS (S : Type u) (T : Type w ) (A : Type v) [LinearOrder T] where
  s: S
  pairs: List (T × A)
  sorted  : pairs.Chain' (fun p q => p.fst < q.fst) -- 時刻が厳密昇順　
  -- ※これはTDVの仕様だが、同一サロゲートに属する, a はTSでしか表せないためこちらで定義する

inductive TSType where
  | StepWiseConstant -- ステップ定数型
  | Continuous -- 連続型
  | Discrete -- 離散型
  | UserDefinedTypeMissingValue --　ユーザ定義型欠損値

/-- Object
オブジェクトはサロゲートとアトリビュートを持つ
-/
structure Obj (S : Type v) (A : Type w) where
  surr : S
  attrs : A

/-- Objects 上での単射性 -/
def InjOn {α : Type u} {β : Type v} (f : α → β) (s : Set α) : Prop :=
  ∀ ⦃x y⦄, x ∈ s → y ∈ s → f x = f y → x = y

/-- Class
  一意のサロゲートを持つ Object の集合を持つ
-/
structure Clazz (S : Type v) (A : Type w) where
  objects      : Set (Obj S A)
  surr_inj     : InjOn (fun o => o.surr) objects  -- 集合上でサロゲートが一意

-- /-- 時系列コレクションの分類 -/
inductive TSCType where
  | discrete          -- 離散的な時点でのみ値が存在
  | stepwise_constant -- 変更されるまで値が一定
  | continuous        -- 時間全体で連続的に値が定義される


/-- 単純なTSC
単純クラスかつ単一の時間ドメイン T・属性ドメイン A に対し、サロゲートに一つのTS を対応させる写像。
-/
structure SimpleTSC
  (S : Type u) (T : Type w) (A : Type v) (C : Clazz S A) [LinearOrder T] where
  ts   : { o : Obj S A // o ∈ C.objects } → TS S T A
  s_ok : ∀ (o : { o : Obj S A // o ∈ C.objects }), (ts o).s = o.val.surr
  -- （この時点では）SimpleTSCもComplexTSCもTSCの単なる特殊化であり例えばSが S1なのか S1 x S2 なのかの違いしかない


 /--
 時系列測定の精度と単位の定義
 粒度階層：秒 < 分 < 時 < 日 < 月 < 年
 TODO: この定義だと時間を正数の順序で表したりカレンダーの階層構造を表すことができていない。
 必要になったら真面目に実装する
  -/
inductive TimeGranularity where
  | second
  | minute
  | hour
  | day
  | month
  | year

/--
寿命

fixed, endpoint=now, startpoint=endpoint-distance　かつ endpont=currenttime みたいな表現が可能
-/
structure Lifespan (T : Type v) [LinearOrder T] where
  start_point : T
  end_point : T
  valid : start_point < end_point


inductive Regularity where
  | regular    -- 規則的な時系列間隔
  | irregular  -- 規則的でない時系列間隔


/-- Time Stamp Collection
同じクラス（または型）に属するオブジェクトの時系列オブジェクトのコレクション
論文ではTSCType、TimeGranularity、Lifespan、Regularityも構成要素に含まれているが、TSCのインスタンス生成やオペレータの定義には不要なので追加していない
-/
structure TSC
  (S : Type u) (T : Type w) (A : Type v) (C : Clazz S A) [LinearOrder T] where
  ts   : { o : Obj S A // o ∈ C.objects } → TS S T A
  s_ok : ∀ (o : { o : Obj S A // o ∈ C.objects }), (ts o).s = o.val.surr

-- complex TSC
-- Tが単一の要素でない場合は、時間的な値が複数の時間シーケンスに関連付けられている状態に対応する
-- 例えば transaction timeとvalid timeを持つ

variable {T : Type v} [LinearOrder T]

-- ある時刻tがlifeSpanの閉区間に存在する
def contains (L : Lifespan T) (t : T) : Prop :=
  L.start_point ≤ t ∧ t ≤ L.end_point

-- TS のすべてのタイムスタンプが寿命 `L` に内包される（= TS が L を満たす)
def respects (ts : TS S T A) (L : Lifespan T) : Prop :=
  ∀ {t a}, (t, a) ∈ ts.pairs → contains L t

-- ある時刻tがTS上の観測地点として現れる
def hasTime (ts : TS S T A) (t : T) : Prop :=
  ∃ a, (t, a) ∈ ts.pairs

-- あるTSの全ての観測地点はLifespanの閉空間に存在する
def supportedWithin (ts : TS S T A) (L : Lifespan T) : Prop :=
  ∀ {t a}, (t, a) ∈ ts.pairs → L.start_point ≤ t ∧ t ≤ L.end_point


abbrev AccountNo := String --明記されていないが簡単に実装するために口座番号をサロゲートキーとする

structure BankAttrs where
  balance : Int

def obj1 : Obj Nat Nat := { surr := 1, attrs := 57 }

abbrev BankClazzVal : Clazz Nat Nat :=
  { objects :=  ({obj1} : Set (Obj Nat Nat)),
    surr_inj := by
      intro x y hx hy hxy
      have hx' : x = obj1 := hx
      have hy' : y = obj1 := hy
      rw [hx', hy'] }

-- OPERATIONS OVER TSCs



structure Predicate (S T A : Type) where
  surr_pred : S → Bool  -- サロゲートに対する述語
  time_pred : T → Bool  -- 時刻に対する述語
  attr_pred : A → Bool  -- 属性値に対する述語

/-- 時間範囲の指定 -/
inductive TimeRange (T : Type) [LinearOrder T] where
  | interval : T → T → TimeRange T  -- 開始時刻から終了時刻まで
  | last_n : Nat → T → TimeRange T  -- 参照時刻から過去n個
  | next_n : Nat → T → TimeRange T  -- 参照時刻から未来n個

/-- 時間範囲に時刻が含まれるかの判定 -/
def TimeRange.contains {T : Type} [LinearOrder T] (range : TimeRange T) (t : T) : Bool :=
  match range with
  | TimeRange.interval start_t end_t => (start_t ≤ t) && (t ≤ end_t)
  | TimeRange.last_n _ _ => true  -- 簡略化：実装では参照時刻から過去n個を取得
  | TimeRange.next_n _ _ => true  -- 簡略化：実装では参照時刻から未来n個を取得

/-- TSから条件を満たすペアをフィルタリング -/
def filterPairs {S T A : Type} [LinearOrder T] (ts : TS S T A) (pred : Predicate S T A) : List (T × A) :=
  ts.pairs.filter (fun (t, a) => pred.surr_pred ts.s && pred.time_pred t && pred.attr_pred a)

lemma filtered_sorted {S T A : Type} [LinearOrder T] (ts : TS S T A) (pred : Predicate S T A) :
  (filterPairs ts pred).Chain' (fun p q => p.fst < q.fst) := by
  unfold filterPairs
  have h_trans : IsTrans (T × A) (fun p q => p.fst < q.fst) := by
    constructor
    intro a b c hab hbc
    exact lt_trans hab hbc
  have h_sublist : (ts.pairs.filter (fun (t, a) => pred.surr_pred ts.s && pred.time_pred t && pred.attr_pred a)).Sublist ts.pairs :=
    List.filter_sublist
  exact List.Chain'.sublist ts.sorted h_sublist

/-- SELECTION演算子 -/
-- 実装の簡易さのためにカレンダーでのクエリは行わない
def selection {S T A : Type} [LinearOrder T] (ts : TS S T A) (pred : Predicate S T A) : TS S T A :=
  { s := ts.s,
    pairs := filterPairs ts pred,
    sorted := filtered_sorted ts pred }

-- 具体的な述語の定義

/-- 時刻が特定の範囲内にある述語 -/
def timeInRange {S T A : Type} [LinearOrder T] (start_t end_t : T) : Predicate S T A :=
  { surr_pred := fun _ => true,
    time_pred := fun t => (start_t ≤ t) && (t ≤ end_t),
    attr_pred := fun _ => true }

/-- 属性値が特定の値以上である述語（Natに特化） -/
def attrGE (min_val : Nat) : Predicate Nat Nat Nat :=
  { surr_pred := fun _ => true,
    time_pred := fun _ => true,
    attr_pred := fun a => min_val ≤ a }

/-- サロゲートが特定の値と等しい述語 -/
def surrEq {S T A : Type} [LinearOrder T] [DecidableEq S] (target_s : S) : Predicate S T A :=
  { surr_pred := fun s => s == target_s,
    time_pred := fun _ => true,
    attr_pred := fun _ => true }

-- TSCの例を定義
def sampleTSC : TSC Nat Nat Nat BankClazzVal :=
  { ts := fun o =>
    { s := o.val.surr,
      pairs := [(1, 57), (4, 50), (6, 65), (9, 60)],
      sorted := by decide
    },
    s_ok := by intros; rfl }

-- 使用例

def sampleTS : TS Nat Nat Nat :=
  sampleTSC.ts ⟨obj1, rfl⟩

-- 使用例1：時刻4から9までの範囲でのSELECTION
def timeRangeSelection : TS Nat Nat Nat :=
  let time_pred := timeInRange 4 9
  selection sampleTS time_pred

-- 使用例2：残高が55以上のデータのSELECTION
def balanceSelection : TS Nat Nat Nat :=
  let attr_pred := attrGE 55
  selection sampleTS attr_pred

-- 複合条件の例：時刻4以降かつ残高60以上
def complexPredicate : Predicate Nat Nat Nat :=
  { surr_pred := fun _ => true,
    time_pred := fun t => 4 ≤ t,
    attr_pred := fun a => 60 ≤ a }

def complexSelection : TS Nat Nat Nat :=
  selection sampleTS complexPredicate

-- 結果の確認用関数
#eval! timeRangeSelection.pairs  -- [(4, 50), (6, 65), (9, 60)]
#eval! balanceSelection.pairs    -- [(1, 57), (6, 65), (9, 60)]
#eval! complexSelection.pairs    -- [(9, 60)]
