permit(
  principal == a::"",
  action in [Action::"action",Action::"action",Action::"action"],
  resource in a::""
) when {
  true && (((a::"" == a::"") == (a::"" == a::"")) == (principal == principal))
};
