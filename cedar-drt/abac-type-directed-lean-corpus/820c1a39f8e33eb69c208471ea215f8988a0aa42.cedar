permit(
  principal == a::"",
  action,
  resource
) when {
  true && ([if true then action else action, if true then action else action, a::"\0\0\0\0y\0\0\u{13}\0\0"].contains(Action::"action"))
};
