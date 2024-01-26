@Yvvvvvvvss("6667")
permit(
  principal == a::"\0\0___j___________*________",
  action,
  resource is a in a::"\0\0___j___________*________"
) when {
  true && (!(action in [action, principal, principal]))
};
