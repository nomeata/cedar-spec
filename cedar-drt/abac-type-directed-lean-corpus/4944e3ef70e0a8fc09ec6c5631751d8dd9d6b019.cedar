permit(
  principal,
  action == Action::"action",
  resource
) when {
  (true && (a::"" in (if (principal in principal) then a::"" else a::""))) && (a::"" in principal)
};
