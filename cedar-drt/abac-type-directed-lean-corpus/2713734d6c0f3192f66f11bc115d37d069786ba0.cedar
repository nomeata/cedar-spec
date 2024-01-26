permit(
  principal == a::"",
  action == Action::"action",
  resource in a::""
) when {
  (true && (x::"ffff" in x::"")) && true
};
