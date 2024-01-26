permit(
  principal == a::"",
  action,
  resource
) when {
  true && (if context then a::"" else a::"")
};
