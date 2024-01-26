permit(
  principal == a::"",
  action == Action::"action",
  resource
) when {
  ((true && ({} has "\0\0\0")) && false) && false
};
