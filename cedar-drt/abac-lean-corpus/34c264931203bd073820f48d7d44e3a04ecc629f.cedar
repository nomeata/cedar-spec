permit(
  principal,
  action,
  resource is a
) when {
  (true && (a::"" == ((Action::"action" in a::"\u{2}\0") + a::"\u{2}\0"))) && a::""
};
