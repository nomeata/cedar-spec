permit(
  principal is a in a::"\0\0\0\0\0\0\0",
  action == Action::"action",
  resource is a in a::""
) when {
  (true && (Action::"action" in (principal["Khhh"]))) && principal
};
