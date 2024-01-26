forbid(
  principal == a::"6",
  action,
  resource == a::"6"
) when {
  true && ((a::"" has "") || true)
};
