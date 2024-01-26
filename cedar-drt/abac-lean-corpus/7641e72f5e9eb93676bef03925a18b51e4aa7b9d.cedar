permit(
  principal == a::"",
  action in [Action::"action",Action::"action"],
  resource == a::""
) when {
  true && (if ((if a::"" then a::"" else a::"") == a::"") then principal else principal)
};
