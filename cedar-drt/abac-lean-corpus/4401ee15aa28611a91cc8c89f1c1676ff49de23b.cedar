forbid(
  principal == a::"j\0j\0",
  action in [Action::"action"],
  resource == a::"j\0j\0"
) when {
  (true && (![])) && resource
};
