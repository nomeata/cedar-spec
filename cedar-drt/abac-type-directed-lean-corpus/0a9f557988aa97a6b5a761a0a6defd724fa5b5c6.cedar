permit(
  principal,
  action == Action::"action",
  resource
) when {
  ((true && ({"": principal, "\0": false, "5\0": principal}["\0"])) && false) && false
};
