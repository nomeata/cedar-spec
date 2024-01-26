permit(
  principal is a in a::"\0j&j&jj\0\0",
  action in [Action::"action"],
  resource == a::"\0j&j&jj\0\0"
) when {
  (true && (Action::"action" == action)) && false
};
