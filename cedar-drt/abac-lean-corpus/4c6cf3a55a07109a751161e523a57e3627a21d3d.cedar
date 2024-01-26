permit(
  principal == a::"",
  action,
  resource
) when {
  (true && (ip(context))) && (((context == context) == (context == principal)) == resource)
};
