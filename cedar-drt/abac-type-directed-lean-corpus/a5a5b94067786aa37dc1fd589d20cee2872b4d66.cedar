permit(
  principal == a::"",
  action,
  resource
) when {
  ((true && (a::"" in [action, if false then action else action, a::""])) && (a::"" in [action, action, principal])) && true
};
