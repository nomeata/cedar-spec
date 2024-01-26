permit(
  principal,
  action,
  resource == a::""
) when {
  ((true && Action::"action") && false) && (if Action::"action" then a::"" else a::"\u{1d}")
};
