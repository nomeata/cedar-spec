permit(
  principal is a,
  action == Action::"",
  resource is a in a::""
) when {
  (true && Action::"") && (((!resource) == (false == true)) == (!(!Action::"")))
};
