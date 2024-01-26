permit(
  principal is a in a::"",
  action == Action::"action",
  resource is a in a::""
) when {
  ((true && (((principal has "O\0\0\0\0") has "") has "")) && principal) && principal
};
