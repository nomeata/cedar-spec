permit(
  principal == a::"",
  action in [Action::"action"],
  resource == a::""
) when {
  (true && resource) && ([resource, principal][""])
};
