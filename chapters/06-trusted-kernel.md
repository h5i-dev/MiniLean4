# 第6章 Trusted Kernel: 小さな検証器の境界

## 到達目標

証明の発見・構築と証明の検証を分離する。証明を採用する唯一の経路を理解する。

## 理論

kernel は他の処理に頼らず `⊢ t : T` を判定する。elaborator や tactics は任意に複雑でもよいが、最後には proof term を渡さなければならない。

## 実装

`Environment::theorem` は statement が型として妥当か検査し、空文脈で `check(proof,statement)` に成功したときだけ記録する。エラー時は登録されない。これは外部公理の登録 API を公開しない小さな閉じた環境である。

**注意:** 教材 kernel の soundness を形式的に証明したわけではない。名前ベースの置換・normalization fuel・universes 等の信頼境界と制約を実際の Lean と混同しない。

## 演習

`0 = 1` を `Refl(0)` で偽装してみよ。kernel はその失敗を明確に返すべきである。次に `Environment::theorem` で登録されないことを確認する。

## テスト

`cargo test reject_fake_equality` と `cargo test env_only_accepts_checked`。
