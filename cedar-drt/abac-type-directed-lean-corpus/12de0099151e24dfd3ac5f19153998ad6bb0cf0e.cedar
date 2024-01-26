forbid(
  principal in a::"",
  action == Action::"action",
  resource in a::""
) when {
  (true && (principal is a)) && (principal is a)
};
