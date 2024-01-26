@t("j")
forbid(
  principal,
  action,
  resource == a::"j"
) when {
  true && (!action)
};
