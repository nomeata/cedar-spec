permit(
  principal == a::"",
  action,
  resource
) when {
  true && ([if true then action else action, if false then action else action, if true then action else action].contains(Action::"action"))
};
