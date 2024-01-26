permit(
  principal == a::"",
  action,
  resource
) when {
  (true && principal) && ((21845 is a) == "")
};
