@O("\0\0")
@r("")
forbid(
  principal is a in a::"",
  action in [Action::"action"],
  resource == a::"\0forbid\0"
) when {
  true
};
