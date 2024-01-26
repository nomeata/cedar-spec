permit(
  principal is a in a::"\0\0\0",
  action in [Action::"action"],
  resource == a::"\0\0\0"
) when {
  true && (if (!(principal in action)) then (false == (principal in principal)) else false)
};
