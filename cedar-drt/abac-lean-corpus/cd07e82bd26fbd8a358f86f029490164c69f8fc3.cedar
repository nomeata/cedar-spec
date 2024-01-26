permit(
  principal,
  action,
  resource is a in a::"\0"
) when {
  (true && slacq::"") && false
};
