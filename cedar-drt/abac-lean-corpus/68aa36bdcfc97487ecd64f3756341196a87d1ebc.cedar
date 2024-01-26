forbid(
  principal is a in a::"jj\0",
  action in [Action::"action"],
  resource == a::"jj\0"
) when {
  (true && ((context <= false) in a::"")) && action
};
