permit(
  principal,
  action == Action::"action",
  resource
) when {
  ((true && ({"\0\0": resource, "\0": false, "": false}["\0"])) && false) && false
};
