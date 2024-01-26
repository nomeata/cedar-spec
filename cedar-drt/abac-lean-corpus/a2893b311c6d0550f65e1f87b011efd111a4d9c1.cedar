@Ehp3wCr0000000("\0")
forbid(
  principal in a::"",
  action in [Action::"action"],
  resource == a::""
) when {
  (true && Action::"action") && action
};
