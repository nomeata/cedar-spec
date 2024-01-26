forbid(
  principal,
  action in [Action::"action"],
  resource in a::"\0jiji\njzlkj"
) when {
  (true && action) && (!context)
};
