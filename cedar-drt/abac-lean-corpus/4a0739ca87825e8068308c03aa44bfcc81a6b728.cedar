permit(
  principal == a::"",
  action in [Action::"action"],
  resource is a
) when {
  ((true && (((a::"" has "") has "") has "")) && (principal has "jj")) && principal
};
