permit(
  principal,
  action,
  resource == a::"6"
) when {
  (true && (Action::"action" in (if ([].containsAny([])) then a::"6" else a::"6"))) && true
};
