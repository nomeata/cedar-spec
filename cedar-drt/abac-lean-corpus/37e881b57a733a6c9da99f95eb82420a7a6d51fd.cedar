permit(
  principal,
  action,
  resource in a::"j"
) when {
  (true && a::"j") && (!principal)
};
