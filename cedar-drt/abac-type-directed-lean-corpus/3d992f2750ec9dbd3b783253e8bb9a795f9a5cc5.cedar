permit(
  principal == a::"666",
  action,
  resource
) when {
  (true && (a::"666" in (if (principal in []) then [principal, principal] else (if true then [] else [])))) && false
};
